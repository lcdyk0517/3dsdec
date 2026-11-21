#define _GNU_SOURCE
#define _FILE_OFFSET_BITS 64
#include <openssl/evp.h>
#include <openssl/sha.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <sys/stat.h>
#include <unistd.h>

#define NO_CRYPTO 4
#define FIXED_KEY 1
#define SEED_CRYPTO 0x20
struct seed_entry { uint64_t title; uint8_t seed[16]; };
struct keys {
    uint8_t x[64][16], common[256][16], title[16], fixed[16];
    unsigned char have_x[64], have_common[256];
    int have_title, have_fixed;
    struct seed_entry *seeds;
    unsigned seed_count;
};
struct content { uint64_t off, size; uint16_t index, type; uint8_t *record; };
struct image {
    int cia;
    uint64_t size, tmd_off;
    uint8_t *tmd, *body, ticket_id[8], encrypted_key[16];
    uint8_t *ticket;
    uint32_t ticket_size;
    uint64_t ticket_num;
    unsigned common_index, count;
    struct content *contents;
};
struct ncch {
    uint8_t h[512];
    uint64_t off, size, exefs, exefs_size, romfs, romfs_size, exefs_hash_size, romfs_hash_size;
    uint32_t exheader;
};
static int error(const char *fmt, ...) {
    va_list args; va_start(args, fmt);
    fputs("3dsdec: ", stderr); vfprintf(stderr, fmt, args); fputc('\n', stderr);
    va_end(args); return -1;
}
static uint16_t le16(const uint8_t *p) { return p[0] | (uint16_t)p[1] << 8; }
static uint16_t be16(const uint8_t *p) { return (uint16_t)p[0] << 8 | p[1]; }
static uint32_t le32(const uint8_t *p) { return p[0] | (uint32_t)p[1]<<8 | (uint32_t)p[2]<<16 | (uint32_t)p[3]<<24; }
static uint32_t be32(const uint8_t *p) { return (uint32_t)p[0]<<24 | (uint32_t)p[1]<<16 | (uint32_t)p[2]<<8 | p[3]; }
static uint64_t le64(const uint8_t *p) { return le32(p) | (uint64_t)le32(p+4)<<32; }
static uint64_t be64(const uint8_t *p) { return (uint64_t)be32(p)<<32 | be32(p+4); }
static void put_be16(uint8_t *p, uint16_t n) { p[0]=n>>8; p[1]=n; }
static int within(uint64_t off, uint64_t len, uint64_t total) { return off<=total && len<=total-off; }
static uint64_t align64(uint64_t n) { return (n+63)&~UINT64_C(63); }
static int read_at(FILE *f, uint64_t off, void *p, size_t n) {
    if (off>INT64_MAX || fseeko(f, (off_t)off, SEEK_SET) || fread(p,1,n,f)!=n)
        return error("read failed at offset %llu", (unsigned long long)off);
    return 0;
}
static int write_at(FILE *f, uint64_t off, const void *p, size_t n) {
    if (off>INT64_MAX || fseeko(f, (off_t)off, SEEK_SET) || fwrite(p,1,n,f)!=n)
        return error("write failed at offset %llu", (unsigned long long)off);
    return 0;
}
static unsigned signature_body(const uint8_t *p, size_t n) {
    if (n<4) return 0;
    switch (be32(p)) {
        case 0x10000: case 0x10003: return 0x240;
        case 0x10001: case 0x10004: return 0x140;
        case 0x10002: case 0x10005: return 0x7c;
        default: return 0;
    }
}
static int validate_ticket(const uint8_t *ticket, unsigned base, size_t size) {
    if (!base || !within(base,0x178,size) || ticket[base+0x7c]!=1)
        return error("invalid ticket version or truncated ticket body");
    const uint8_t *ext=ticket+base+0x164;
    uint32_t total=be32(ext+4), sections=be32(ext+8);
    unsigned count=be16(ext+12), stride=be16(ext+14);
    if (be16(ext)!=1 || be16(ext+2)!=20 || sections!=20 || stride!=20 ||
        total<20 || !within(base+0x164,total,size) || !within(sections,(uint64_t)count*stride,total))
        return error("invalid ticket extension");
    for (unsigned i=0;i<count;++i) {
        const uint8_t *s=ext+sections+i*stride;
        uint64_t off=be32(s), records=be32(s+4), entry=be32(s+8), len=be32(s+12);
        if (off<sections+(uint64_t)count*stride || records*entry!=len || !within(off,len,total))
            return error("invalid ticket section bounds");
    }
    return 0;
}
static int hash_region(FILE *f, uint64_t off, uint64_t len, uint8_t hash[32]) {
    uint8_t buf[65536]; EVP_MD_CTX *ctx=EVP_MD_CTX_new();
    int ok=ctx && EVP_DigestInit_ex(ctx, EVP_sha256(), NULL);
    while (ok && len) {
        size_t n=len<sizeof buf ? (size_t)len : sizeof buf;
        if (read_at(f,off,buf,n)) { ok=0; break; }
        ok=EVP_DigestUpdate(ctx,buf,n); off+=n; len-=n;
    }
    unsigned n=0;
    if (ok) ok=EVP_DigestFinal_ex(ctx,hash,&n) && n==32;
    EVP_MD_CTX_free(ctx);
    return ok ? 0 : error("SHA-256 failed");
}
static int verify_region(FILE *f, uint64_t off, uint64_t len, const uint8_t want[32], const char *label) {
    uint8_t got[32];
    if (hash_region(f,off,len,got)) return -1;
    return memcmp(got,want,32) ? error("%s hash mismatch (wrong key or corrupt input)",label) : 0;
}
static int tmd_hashes(struct image *img, int update) {
    uint8_t *b=img->body, hash[32]; unsigned count=be16(b+0x9e);
    uint8_t *covered=calloc(count ? count : 1,1);
    if (!covered) return error("out of memory");
    int result=-1;
    for (unsigned i=0;i<64;++i) {
        uint8_t *info=b+0xc4+i*0x24;
        unsigned start=be16(info), n=be16(info+2);
        if (!n) continue;
        if (start>count || n>count-start) { error("invalid TMD content-info range"); goto done; }
        for (unsigned j=start;j<start+n;++j) {
            if (covered[j]) { error("overlapping TMD content-info ranges"); goto done; }
            covered[j]=1;
        }
        SHA256(b+0x9c4+start*48,n*48,hash);
        if (update) memcpy(info+4,hash,32);
        else if (memcmp(info+4,hash,32)) { error("TMD content-info hash mismatch"); goto done; }
    }
    for (unsigned i=0;i<count;++i)
        if (!covered[i]) { error("TMD content record has no hash group"); goto done; }
    SHA256(b+0xc4,0x900,hash);
    if (update) memcpy(b+0xa4,hash,32);
    else if (memcmp(b+0xa4,hash,32)) { error("TMD table hash mismatch"); goto done; }
    result=0;
done:
    free(covered); return result;
}
static int parse_image(FILE *f, struct image *img) {
    struct stat st; uint8_t h[512];
    if (fstat(fileno(f),&st) || !S_ISREG(st.st_mode) || st.st_size<512)
        return error("input is not a regular image file");
    img->size=(uint64_t)st.st_size;
    if (read_at(f,0,h,sizeof h)) return -1;
    if (!memcmp(h+0x100,"NCSD",4)) {
        if (h[0x18e]>20) return error("invalid NCSD media unit");
        uint64_t unit=UINT64_C(512)<<h[0x18e];
        img->contents=calloc(8,sizeof(*img->contents));
        if (!img->contents) return error("out of memory");
        for (unsigned i=0;i<8;++i) {
            uint64_t off=(uint64_t)le32(h+0x120+i*8)*unit, size=(uint64_t)le32(h+0x124+i*8)*unit;
            if (!size) continue;
            if (off<512 || !within(off,size,img->size)) return error("invalid NCSD partition bounds");
            for (unsigned j=0;j<img->count;++j) {
                struct content *c=&img->contents[j];
                if (off<c->off+c->size && c->off<off+size) return error("overlapping NCSD partitions");
            }
            img->contents[img->count++]=(struct content){off,size,(uint16_t)i,0,NULL};
        }
        return img->count ? 0 : error("NCSD contains no partitions");
    }
    if (le32(h)!=0x2020 || le16(h+4)!=0 || le16(h+6)!=0)
        return error("unsupported image (expected standard CIA or NCSD/CCI)");
    img->cia=1;
    uint32_t cert_size=le32(h+8), ticket_size=le32(h+12), tmd_size=le32(h+16);
    uint64_t content_size=le64(h+24), ticket_off=align64(0x2020)+align64(cert_size);
    img->tmd_off=ticket_off+align64(ticket_size);
    uint64_t content_off=img->tmd_off+align64(tmd_size);
    if (ticket_size>65536 || tmd_size>0x310000 || !within(ticket_off,ticket_size,img->size) ||
        !within(img->tmd_off,tmd_size,img->size) || !within(content_off,content_size,img->size) ||
        (le32(h+20) && !within(align64(content_off+content_size),le32(h+20),img->size)))
        return error("invalid CIA section bounds");
    uint8_t *ticket=malloc(ticket_size ? ticket_size : 1);
    img->tmd=malloc(tmd_size ? tmd_size : 1);
    if (!ticket || !img->tmd) { free(ticket); return error("out of memory"); }
    if (read_at(f,ticket_off,ticket,ticket_size) || read_at(f,img->tmd_off,img->tmd,tmd_size)) { free(ticket); return -1; }
    unsigned tb=signature_body(ticket,ticket_size), mb=signature_body(img->tmd,tmd_size);
    if (!mb || !within(mb,0x9c4,tmd_size) || validate_ticket(ticket,tb,ticket_size)) {
        free(ticket); return error("invalid ticket/TMD header");
    }
    memcpy(img->encrypted_key,ticket+tb+0x7f,16); memcpy(img->ticket_id,ticket+tb+0x9c,8);
    img->common_index=ticket[tb+0xb1];
    img->ticket=ticket; img->ticket_size=ticket_size; img->ticket_num=be64(ticket+tb+0x90);
    img->body=img->tmd+mb;
    if (img->body[0x40]!=1 || memcmp(img->body+0x4c,img->ticket_id,8))
        return error("unsupported TMD version or ticket title ID mismatch");
    unsigned count=be16(img->body+0x9e);
    if (!count || !within(mb+0x9c4,(uint64_t)count*48,tmd_size)) return error("invalid TMD content count");
    if (tmd_hashes(img,0)) return -1;
    img->contents=calloc(count,sizeof(*img->contents));
    if (!img->contents) return error("out of memory");
    uint8_t present[8192], seen[8192]={0};
    if (read_at(f,0x20,present,sizeof present)) return -1;
    uint64_t used=0;
    for (unsigned i=0;i<count;++i) {
        uint8_t *r=img->body+0x9c4+i*48;
        uint16_t index=be16(r+4), type=be16(r+6);
        unsigned mask=0x80u>>(index&7);
        if (seen[index>>3]&mask) return error("duplicate TMD content index");
        seen[index>>3]|=mask;
        if (!(present[index>>3]&mask)) continue;
        present[index>>3]&=(uint8_t)~mask;
        uint64_t size=be64(r+8);
        if (!size || (size&15) || !within(used,size,content_size))
            return error("invalid or unsupported unaligned CIA content size");
        img->contents[img->count++]=(struct content){content_off+used,size,index,type,r}; used+=size;
    }
    for (unsigned i=0;i<sizeof present;++i)
        if (present[i]) return error("CIA bitmap references content absent from TMD");
    return used==content_size && img->count ? 0 : error("CIA content size/bitmap mismatch");
}
static int parse_ncch(FILE *f, const struct content *c, struct ncch *n) {
    memset(n,0,sizeof(*n));
    if (c->size<512) return 1;
    if (read_at(f,c->off,n->h,512)) return -1;
    if (memcmp(n->h+0x100,"NCCH",4)) return 1;
    n->off=c->off;
    unsigned version=le16(n->h+0x112);
    if (version!=0 && version!=2) return error("NCCH version %u is unsupported",version);
    if (n->h[0x18e]>20) return error("invalid NCCH media unit");
    uint64_t unit=UINT64_C(512)<<n->h[0x18e];
    n->size=(uint64_t)le32(n->h+0x104)*unit;
    if (n->size<512 || n->size>c->size) return error("invalid NCCH size");
    n->exheader=le32(n->h+0x180);
    if (n->exheader && (n->exheader!=0x400 || !within(0x200,0x800,n->size)))
        return error("unsupported NCCH extended header size");
    n->exefs=(uint64_t)le32(n->h+0x1a0)*unit; n->exefs_size=(uint64_t)le32(n->h+0x1a4)*unit;
    n->exefs_hash_size=(uint64_t)le32(n->h+0x1a8)*unit;
    n->romfs=(uint64_t)le32(n->h+0x1b0)*unit; n->romfs_size=(uint64_t)le32(n->h+0x1b4)*unit;
    n->romfs_hash_size=(uint64_t)le32(n->h+0x1b8)*unit;
    uint64_t end=n->exheader ? 0xa00 : 512;
    if ((n->exefs_size && (n->exefs<end || n->exefs_size<512 || !within(n->exefs,n->exefs_size,n->size) ||
          n->exefs_hash_size<512 || n->exefs_hash_size>n->exefs_size)) ||
        (n->romfs_size && (n->romfs<end || !within(n->romfs,n->romfs_size,n->size) ||
          !n->romfs_hash_size || n->romfs_hash_size>n->romfs_size)) ||
        (n->exefs_size && n->romfs_size && n->exefs<n->romfs+n->romfs_size && n->romfs<n->exefs+n->exefs_size))
        return error("invalid/overlapping NCCH regions");
    return 0;
}
static __uint128_t load128(const uint8_t *p) {
    __uint128_t v=0; for (unsigned i=0;i<16;++i) v=(v<<8)|p[i]; return v;
}
static void store128(__uint128_t v, uint8_t *p) { for (int i=15;i>=0;--i) { p[i]=(uint8_t)v; v>>=8; } }
static __uint128_t rol(__uint128_t v, unsigned n) { return (v<<n)|(v>>(128-n)); }
static void scramble(const uint8_t x[16], const uint8_t y[16], uint8_t key[16]) {
    const __uint128_t c=((__uint128_t)UINT64_C(0x1ff9e9aac5fe0408)<<64)|UINT64_C(0x024591dc5d52768a);
    store128(rol((rol(load128(x),2)^load128(y))+c,87),key);
}
static const uint8_t *find_seed(const struct keys *keys, uint64_t title) {
    for (unsigned i = 0; i < keys->seed_count; ++i)
        if (keys->seeds[i].title == title) return keys->seeds[i].seed;
    return NULL;
}

static int ncch_keys(const struct ncch *n, const struct keys *keys, uint8_t primary[16], uint8_t secondary[16]) {
    if (n->h[0x18f]&FIXED_KEY) {
        if (le64(n->h+0x118)&(UINT64_C(1)<<36)) {
            if (!keys->have_fixed) return error("missing fixedSystemKey in --keys file");
            memcpy(primary,keys->fixed,16);
        } else memset(primary,0,16);
        memcpy(secondary,primary,16); return 0;
    }
    unsigned slot;
    switch (n->h[0x18b]) {
        case 0: slot=0x2c; break; case 1: slot=0x25; break;
        case 0xa: slot=0x18; break; case 0xb: slot=0x1b; break;
        default: return error("unknown NCCH crypto method 0x%02x",n->h[0x18b]);
    }
    if (!keys->have_x[0x2c]) return error("missing NCCH KeyX 0x2C; supply --boot9 or --keys");
    if (!keys->have_x[slot]) return error("missing slot0x%02XKeyX in --keys file",slot);

    uint8_t keyy[16];
    memcpy(keyy, n->h, 16);
    if (n->h[0x18f] & SEED_CRYPTO) {
        uint64_t tid = be64(n->h + 0x118);
        const uint8_t *seed = find_seed(keys, tid);
        if (!seed)
            return error("seed for title %016llX not found; supply --seeddb",
                         (unsigned long long)tid);
        uint8_t in[32], hash[32];
        memcpy(in, n->h, 16);
        memcpy(in + 16, seed, 16);
        SHA256(in, sizeof in, hash);
        memcpy(keyy, hash, 16);
    }

    scramble(keys->x[0x2c],n->h,primary); scramble(keys->x[slot],keyy,secondary); return 0;
}
static int title_key(const struct image *img, const struct keys *keys, uint8_t key[16]) {
    if (keys->have_title) { memcpy(key,keys->title,16); return 0; }
    if (!keys->have_common[img->common_index])
        return error("missing CIA common%u key; supply --keys or --titlekey",img->common_index);
    uint8_t iv[16]={0}, out[32]; memcpy(iv,img->ticket_id,8);
    EVP_CIPHER_CTX *ctx=EVP_CIPHER_CTX_new(); int len=0, last=0;
    int ok=ctx && EVP_DecryptInit_ex(ctx,EVP_aes_128_cbc(),NULL,keys->common[img->common_index],iv) &&
        EVP_CIPHER_CTX_set_padding(ctx,0) && EVP_DecryptUpdate(ctx,out,&len,img->encrypted_key,16) &&
        EVP_DecryptFinal_ex(ctx,out+len,&last) && len+last==16;
    if (ok) memcpy(key,out,16);
    EVP_CIPHER_CTX_free(ctx); return ok ? 0 : error("titlekey decryption failed");
}
static int decrypt_region(FILE *f, uint64_t off, uint64_t size, const EVP_CIPHER *cipher,
                          const uint8_t key[16], const uint8_t iv[16]) {
    uint8_t in[65536], out[65536+EVP_MAX_BLOCK_LENGTH]; EVP_CIPHER_CTX *ctx=EVP_CIPHER_CTX_new();
    int ok=ctx && EVP_DecryptInit_ex(ctx,cipher,NULL,key,iv) && EVP_CIPHER_CTX_set_padding(ctx,0);
    while (ok && size) {
        size_t n=size<sizeof in ? (size_t)size : sizeof in; int len=0;
        if (read_at(f,off,in,n) || !EVP_DecryptUpdate(ctx,out,&len,in,(int)n) ||
            len!=(int)n || write_at(f,off,out,n)) { ok=0; break; }
        off+=n; size-=n;
    }
    int last=0; if (ok) ok=EVP_DecryptFinal_ex(ctx,out,&last) && last==0;
    EVP_CIPHER_CTX_free(ctx); return ok ? 0 : error("AES region decryption failed");
}
static int ncch_region(FILE *f, const struct ncch *n, unsigned region, uint64_t off,
                       uint64_t size, uint64_t skip, const uint8_t key[16]) {
    uint8_t iv[16]={0};
    if (skip&15) return error("unaligned NCCH encryption offset");
    // Counters use each NCCH's little-endian partition ID, not the CIA/NCSD title ID.
    for (unsigned i=0;i<8;++i) iv[i]=n->h[0x10f-i];
    iv[8]=region; store128(load128(iv)+skip/16,iv);
    return decrypt_region(f,n->off+off,size,EVP_aes_128_ctr(),key,iv);
}
static int process_ncch(FILE *f, const struct content *c, const struct keys *keys) {
    struct ncch n; int parsed=parse_ncch(f,c,&n);
    if (parsed) return parsed>0 ? 0 : -1;
    int encrypted=!(n.h[0x18f]&NO_CRYPTO);
    uint8_t primary[16]={0}, secondary[16]={0};
    if (encrypted && ncch_keys(&n,keys,primary,secondary)) return -1;
    if (n.exheader && ((encrypted && ncch_region(f,&n,1,0x200,0x800,0,primary)) ||
        verify_region(f,n.off+0x200,n.exheader,n.h+0x160,"NCCH ExHeader"))) return -1;
    if (n.exefs_size) {
        if (encrypted && ncch_region(f,&n,2,n.exefs,512,0,primary)) return -1;
        uint8_t ex[512]; if (read_at(f,n.off+n.exefs,ex,sizeof ex)) return -1;
        uint64_t offsets[10]={0}, sizes[10]={0};
        for (unsigned i=0;i<10;++i) {
            uint8_t *r=ex+i*16; if (!r[0]) continue;
            uint64_t off=512+(uint64_t)le32(r+8), size=le32(r+12);
            // ExeFS encryption covers each file's 512-byte padded extent; its hash excludes padding.
            uint64_t extent=(size+511)&~UINT64_C(511);
            if ((off&511) || !within(off,extent,n.exefs_size)) return error("invalid ExeFS file bounds");
            for (unsigned j=0;j<i;++j)
                if (sizes[j] && off<offsets[j]+sizes[j] && offsets[j]<off+extent) return error("overlapping ExeFS files");
            offsets[i]=off; sizes[i]=extent;
            int original=!memcmp(r,"icon\0\0\0\0",8) || !memcmp(r,"banner\0\0",8);
            if (encrypted && ncch_region(f,&n,2,n.exefs+off,extent,off,original ? primary : secondary)) return -1;
            if (verify_region(f,n.off+n.exefs+off,size,ex+0x1e0-i*32,"ExeFS file")) return -1;
        }
        if (verify_region(f,n.off+n.exefs,n.exefs_hash_size,n.h+0x1c0,"ExeFS superblock")) return -1;
    }
    if (n.romfs_size && ((encrypted && ncch_region(f,&n,3,n.romfs,n.romfs_size,0,secondary)) ||
        verify_region(f,n.off+n.romfs,n.romfs_hash_size,n.h+0x1e0,"RomFS superblock"))) return -1;
    if (!encrypted) return 0;
    if (!n.exheader && !n.exefs_size && !n.romfs_size) return error("encrypted NCCH has no verifiable content");
    n.h[0x18b]=0; n.h[0x18f]=(n.h[0x18f]&~(FIXED_KEY|SEED_CRYPTO))|NO_CRYPTO;
    return write_at(f,n.off,n.h,sizeof n.h);
}
static int hex_key(const char *s, uint8_t key[16]) {
    if (strlen(s)!=32) return -1;
    for (unsigned i=0;i<16;++i) {
        unsigned v=0;
        for (unsigned j=0;j<2;++j) {
            unsigned char c=s[i*2+j];
            if (c>='0' && c<='9') v=v*16+c-'0';
            else if (c>='a' && c<='f') v=v*16+c-'a'+10;
            else if (c>='A' && c<='F') v=v*16+c-'A'+10;
            else return -1;
        }
        key[i]=v;
    }
    return 0;
}
static char *trim(char *s) {
    s+=strspn(s," \t\r\n"); size_t n=strlen(s);
    while (n && strchr(" \t\r\n",s[n-1])) s[--n]=0;
    return s;
}
static int load_seeddb(const char *path, struct keys *keys) {
    FILE *f = fopen(path, "rb");
    if (!f) return error("cannot open seeddb: %s", strerror(errno));
    uint8_t hdr[16];
    if (fread(hdr, 1, sizeof hdr, f) != sizeof hdr) { fclose(f); return error("seeddb too short"); }
    uint32_t count = le32(hdr);
    if (count > 100000) { fclose(f); return error("seeddb count looks invalid"); }
    keys->seeds = calloc(count ? count : 1, sizeof(*keys->seeds));
    if (!keys->seeds) { fclose(f); return error("out of memory"); }
    for (uint32_t i = 0; i < count; ++i) {
        uint8_t e[32];
        if (fread(e, 1, sizeof e, f) != sizeof e) {
            fclose(f);
            return error("seeddb truncated at entry %u", i);
        }
        keys->seeds[i].title = le64(e);
        memcpy(keys->seeds[i].seed, e + 8, 16);
    }
    fclose(f);
    keys->seed_count = count;
    return 0;
}

static int load_keys(const char *path, struct keys *keys) {
    FILE *f=fopen(path,"r"); if (!f) return error("cannot open key file: %s",strerror(errno));
    char line[512]; int result=0;
    while (fgets(line,sizeof line,f)) {
        char *s=trim(line), *comment=strchr(s,'#'); if (comment) *comment=0;
        s=trim(s); if (!*s) continue;
        char *eq=strchr(s,'=');
        if (!eq) { result=error("key file requires name = 32 hex digits"); break; }
        *eq++=0; char *name=trim(s), *value=trim(eq);
        unsigned slot=0; int end=0; uint8_t *dest=NULL;
        if (sscanf(name,"slot0x%xKeyX%n",&slot,&end)==1 && end>0 && !name[end] && slot<64) {
            dest=keys->x[slot]; keys->have_x[slot]=1;
        } else if ((end=0,sscanf(name,"common%u%n",&slot,&end))==1 && end>0 && !name[end] && slot<256) {
            dest=keys->common[slot]; keys->have_common[slot]=1;
        } else if (!strcmp(name,"fixedSystemKey")) { dest=keys->fixed; keys->have_fixed=1; }
        else { result=error("unrecognized key name in --keys file"); break; }
        if (hex_key(value,dest)) { result=error("invalid key encoding (expected 32 hex digits)"); break; }
    }
    if (ferror(f)) result=error("key file read failed");
    fclose(f); return result;
}
static int load_boot9(const char *path, struct keys *keys) {
    FILE *f=fopen(path,"rb"); if (!f) return error("cannot open boot9: %s",strerror(errno));
    struct stat st; int result=-1;
    if (fstat(fileno(f),&st) || (st.st_size!=0x8000 && st.st_size!=0x10000))
        error("boot9 must be a 32 KiB protected or 64 KiB full dump");
    else {
        result=read_at(f,0x59d0+(st.st_size==0x10000 ? 0x8000 : 0),keys->x[0x2c],16);
        if (!result) keys->have_x[0x2c]=1;
    }
    fclose(f); return result;
}
static int load_titlekey(const char *path, struct keys *keys) {
    FILE *f=fopen(path,"rb"); if (!f) return error("cannot open titlekey file: %s",strerror(errno));
    int ok=fread(keys->title,1,16,f)==16 && fgetc(f)==EOF && !ferror(f); fclose(f);
    if (!ok) return error("--titlekey must contain exactly 16 binary bytes");
    keys->have_title=1; return 0;
}
static int inspect(FILE *f, const struct image *img, const struct keys *keys, int preflight) {
    int encrypted=0; const char *kind=img->cia ? "cia" : "original";
    for (unsigned i=0;i<img->count;++i) {
        const struct content *c=&img->contents[i];
        if (img->cia && (c->type&1)) {
            encrypted=1; uint8_t key[16];
            if (preflight && title_key(img,keys,key)) return -1;
            continue;
        }
        struct ncch n; int parsed=parse_ncch(f,c,&n);
        if (parsed<0) return -1;
        if (parsed>0) { if (!img->cia) return error("NCSD partition is not NCCH"); continue; }
        if (!(n.h[0x18f]&NO_CRYPTO)) {
            encrypted=1;
            if (!img->cia) kind=n.h[0x18f]&SEED_CRYPTO ? "seed" : n.h[0x18f]&FIXED_KEY ? "fixed" : "original";
            uint8_t p[16],s[16]; if (preflight && ncch_keys(&n,keys,p,s)) return -1;
        }
    }
    if (!preflight) { if (encrypted) printf("encrypted:%s\n",kind); else puts("decrypted"); }
    return encrypted;
}

static int wrap_cci(FILE *cia, const char *outpath, const struct image *img) {
    struct part { uint16_t index; uint64_t size; uint8_t id[8]; } parts[3];
    unsigned count = 0;
    for (unsigned want = 0; want < 3; ++want) {
        const struct content *c = NULL;
        for (unsigned i = 0; i < img->count; ++i)
            if (img->contents[i].index == want) c = &img->contents[i];
        if (!c) continue;
        uint8_t h[512];
        if (read_at(cia, c->off, h, sizeof h)) return -1;
        if (memcmp(h + 0x100, "NCCH", 4)) continue;
        if (h[0x18e] > 20) return error("invalid NCCH media unit");
        uint64_t size = (uint64_t)le32(h + 0x104) * (UINT64_C(512) << h[0x18e]);
        if (!size || size > c->size) return error("invalid NCCH size in CIA content %u", want);
        parts[count].index = (uint16_t)want;
        parts[count].size = size;
        memcpy(parts[count].id, h + 0x108, 8);
        ++count;
    }
    if (!count || parts[0].index != 0)
        return error("CIA has no main NCCH; cannot build a bootable CCI");
    uint8_t hdr[512] = {0};
    uint64_t off = sizeof hdr;
    memcpy(hdr + 0x100, "NCSD", 4);
    memcpy(hdr + 0x108, img->ticket_id, 8);
    for (unsigned i = 0; i < count; ++i) {
        off = align64(off);
        if (off / 512 > UINT32_MAX || parts[i].size / 512 > UINT32_MAX)
            return error("CCI too large");
        hdr[0x120 + i * 8 + 0] = (uint8_t)(off / 512);
        hdr[0x120 + i * 8 + 1] = (uint8_t)(off / 512 >> 8);
        hdr[0x120 + i * 8 + 2] = (uint8_t)(off / 512 >> 16);
        hdr[0x120 + i * 8 + 3] = (uint8_t)(off / 512 >> 24);
        uint32_t units = (uint32_t)(parts[i].size / 512);
        hdr[0x124 + i * 8 + 0] = (uint8_t)units;
        hdr[0x124 + i * 8 + 1] = (uint8_t)(units >> 8);
        hdr[0x124 + i * 8 + 2] = (uint8_t)(units >> 16);
        hdr[0x124 + i * 8 + 3] = (uint8_t)(units >> 24);
        memcpy(hdr + 0x190 + i * 8, parts[i].id, 8);
        off += parts[i].size;
    }
    uint32_t total = (uint32_t)(off / 512);
    hdr[0x104] = (uint8_t)total; hdr[0x105] = (uint8_t)(total >> 8);
    hdr[0x106] = (uint8_t)(total >> 16); hdr[0x107] = (uint8_t)(total >> 24);
    char *tmp = malloc(strlen(outpath) + 16);
    if (!tmp) return error("out of memory");
    sprintf(tmp, "%s.part.XXXXXX", outpath);
    int fd = mkstemp(tmp);
    if (fd < 0) { free(tmp); return error("cannot create output: %s", strerror(errno)); }
    FILE *out = fdopen(fd, "w+b");
    if (!out) { close(fd); unlink(tmp); free(tmp); return error("fdopen failed"); }
    int result = -1;
    uint8_t buf[65536];
    if (write_at(out, 0, hdr, sizeof hdr)) goto done;
    for (unsigned i = 0; i < count; ++i) {
        const struct content *c = NULL;
        for (unsigned j = 0; j < img->count; ++j)
            if (img->contents[j].index == parts[i].index) c = &img->contents[j];
        if (!c) { error("internal content lookup failed"); goto done; }
        uint64_t left = parts[i].size, src = c->off, dst = (uint64_t)(hdr[0x120 + i * 8] | hdr[0x120 + i * 8 + 1] << 8 |
                        hdr[0x120 + i * 8 + 2] << 16 | hdr[0x120 + i * 8 + 3] << 24) * 512;
        while (left) {
            size_t n = left < sizeof buf ? (size_t)left : sizeof buf;
            if (read_at(cia, src, buf, n) || write_at(out, dst, buf, n)) goto done;
            src += n; dst += n; left -= n;
        }
    }
    if (fflush(out) || fsync(fileno(out))) { error("flushing output failed"); goto done; }
    if (fclose(out)) { out = NULL; error("closing output failed"); goto done; }
    out = NULL;
    if (renameat2(AT_FDCWD, tmp, AT_FDCWD, outpath, RENAME_NOREPLACE)) {
        error("publishing output failed: %s", strerror(errno)); goto done;
    }
    fprintf(stderr, "3dsdec: wrote %s (CCI)\n", outpath);
    result = 0;
done:
    if (out) fclose(out);
    if (result) unlink(tmp);
    free(tmp);
    return result;
}
static int decrypt_image(FILE *in, const char *outpath, struct image *img, const struct keys *keys, int wrap) {
    if (inspect(in,img,keys,1)<0) return -1;
    struct stat original,final,existing;
    if (fstat(fileno(in),&original)) return error("cannot stat input");
    if (!lstat(outpath,&existing)) return error("output exists; refusing to overwrite");
    if (errno!=ENOENT) return error("cannot inspect output: %s",strerror(errno));
    char *tmp=malloc(strlen(outpath)+16); if (!tmp) return error("out of memory");
    sprintf(tmp,"%s.part.XXXXXX",outpath); int fd=mkstemp(tmp);
    if (fd<0) { free(tmp); return error("cannot create temporary output: %s",strerror(errno)); }
    FILE *out=fdopen(fd,"w+b");
    if (!out) { close(fd); unlink(tmp); free(tmp); return error("fdopen failed"); }
    int result=-1; uint8_t buf[65536];
    for (uint64_t pos=0;pos<img->size;) {
        size_t len=img->size-pos<sizeof buf ? (size_t)(img->size-pos) : sizeof buf;
        if (read_at(in,pos,buf,len) || write_at(out,pos,buf,len)) goto done;
        pos+=len;
    }
    for (unsigned i=0;i<img->count;++i) {
        struct content *c=&img->contents[i];
        fprintf(stderr,"3dsdec: content %u (%u/%u)\n",c->index,i+1,img->count);
        if (img->cia && (c->type&1)) {
            uint8_t key[16],iv[16]={0}; put_be16(iv,c->index);
            if (title_key(img,keys,key) || decrypt_region(out,c->off,c->size,EVP_aes_128_cbc(),key,iv)) goto done;
        }
        // TMD hashes cover bytes after outer CBC removal, before inner NCCH decryption.
        if (img->cia && verify_region(out,c->off,c->size,c->record+16,"CIA content")) goto done;
        if (process_ncch(out,c,keys)) goto done;
        if (img->cia) {
            put_be16(c->record+6,c->type&~1u);
            if (hash_region(out,c->off,c->size,c->record+16)) goto done;
        }
    }
    if (img->cia) {
        if (tmd_hashes(img,1)) goto done;
        size_t len=(size_t)(img->body-img->tmd)+0x9c4+(size_t)be16(img->body+0x9e)*48;
        if (write_at(out,img->tmd_off,img->tmd,len)) goto done;
    }
    if (fstat(fileno(in),&final) || original.st_size!=final.st_size ||
        original.st_mtim.tv_sec!=final.st_mtim.tv_sec || original.st_mtim.tv_nsec!=final.st_mtim.tv_nsec) {
        error("input changed during decryption"); goto done;
    }
    if (fflush(out) || fsync(fileno(out))) { error("flushing output failed"); goto done; }
    if (wrap) {
        if (wrap_cci(out, outpath, img)) goto done;
        if (fclose(out)) { out=NULL; error("closing output failed"); goto done; }
        out=NULL; unlink(tmp); result=0; goto done;
    }
    if (fclose(out)) { out=NULL; error("closing output failed"); goto done; }
    out=NULL;
    if (renameat2(AT_FDCWD,tmp,AT_FDCWD,outpath,RENAME_NOREPLACE)) {
        error("publishing output failed: %s",strerror(errno)); goto done;
    }
    fprintf(stderr,"3dsdec: wrote %s%s\n",outpath,img->cia ? " (decrypted CIA; signatures are not re-signed)" : "");
    result=0;
done:
    if (out) fclose(out);
    if (result) unlink(tmp);
    free(tmp); return result;
}

static int mkdir_p(const char *path) {
    char tmp[4096];
    if (strlen(path) >= sizeof tmp) return error("path too long");
    strcpy(tmp, path);
    for (char *p = tmp + 1; *p; ++p) {
        if (*p != '/') continue;
        *p = 0;
        if (mkdir(tmp, 0755) && errno != EEXIST) return error("cannot create %s: %s", tmp, strerror(errno));
        *p = '/';
    }
    if (mkdir(tmp, 0755) && errno != EEXIST) return error("cannot create %s: %s", tmp, strerror(errno));
    return 0;
}
static int copy_range(FILE *in, uint64_t off, uint64_t size, const char *dest) {
    FILE *out = fopen(dest, "wb");
    uint8_t buf[65536];
    if (!out) return error("cannot create %s: %s", dest, strerror(errno));
    while (size) {
        size_t n = size < sizeof buf ? (size_t)size : sizeof buf;
        if (read_at(in, off, buf, n) || fwrite(buf, 1, n, out) != n) {
            fclose(out); unlink(dest); return error("copy to %s failed", dest);
        }
        off += n; size -= n;
    }
    if (fclose(out)) { unlink(dest); return error("closing %s failed", dest); }
    return 0;
}
/* Install a decrypted add-on (DLC) or update CIA into Azahar's emulated
 * storage, matching Service::AM::GetTitleContentPath:
 *   title/<high>/<low>/content/<cid>.app, 00000000/ when content 1 is Optional.
 * DLC lives on SDMC (media_type=1), updates live in NAND (media_type=0);
 * both tickets go to the NAND dbs. */
static int install_title(FILE *in, struct image *img, const struct keys *keys,
                         const char *userdir, int dlc) {
    if (!img->cia) return error(dlc ? "--install-dlc expects a CIA"
                                    : "--install-update expects a CIA");
    uint64_t tid = be64(img->body + 0x4c);
    uint32_t hi = (uint32_t)(tid >> 32);
    if (dlc && hi != 0x0004008c)
        return error("not a DLC title (title id %016llX)", (unsigned long long)tid);
    if (!dlc && hi != 0x0004000e)
        return error("not an update title (title id %016llX)", (unsigned long long)tid);
    char tmp[4096];
    snprintf(tmp, sizeof tmp, "%s/.3dsdec-dlc-XXXXXX", userdir);
    int fd = mkstemp(tmp);
    if (fd < 0) return error("cannot create temporary CIA: %s", strerror(errno));
    close(fd); unlink(tmp);
    if (decrypt_image(in, tmp, img, keys, 0)) return -1;
    FILE *dec = fopen(tmp, "rb");
    if (!dec) { unlink(tmp); return error("cannot reopen decrypted CIA"); }
    struct image d = {0};
    int result = -1;
    if (parse_image(dec, &d)) goto done;
    unsigned count = be16(d.body + 0x9e);
    int subdir = count > 1 && (be16(d.body + 0x9c4 + 48 + 6) & 0x4000);
    char dir[4096];
    /* DLC (AddOnContents) live on SDMC, not NAND: am:GetDLCTitleInfos(media_type=1)
     * resolves title/<hi>/<lo> under sdmc/Nintendo 3DS/<system id>/<sdcard id>/.
     * Updates are NAND titles (media_type=0): nand/<id>/title/<hi>/<lo>/. */
    if (dlc)
        snprintf(dir, sizeof dir,
                 "%s/sdmc/Nintendo 3DS/00000000000000000000000000000000/"
                 "00000000000000000000000000000000/title/%08x/%08x/content",
                 userdir, (unsigned)(tid >> 32), (unsigned)tid);
    else
        snprintf(dir, sizeof dir,
                 "%s/nand/00000000000000000000000000000000/title/%08x/%08x/content",
                 userdir, (unsigned)(tid >> 32), (unsigned)tid);
    if (mkdir_p(dir)) goto done;
    char path[8192];
    snprintf(path, sizeof path, "%s/00000000.tmd", dir);
    size_t tmd_len = (size_t)(d.body - d.tmd) + 0x9c4 + (size_t)count * 48;
    FILE *tf = fopen(path, "wb");
    if (!tf || fwrite(d.tmd, 1, tmd_len, tf) != tmd_len || fclose(tf)) {
        if (tf) fclose(tf);
        error("cannot write %s", path);
        goto done;
    }
    if (subdir) {
        snprintf(path, sizeof path, "%s/00000000", dir);
        if (mkdir_p(path)) goto done;
    }
    for (unsigned i = 0; i < d.count; ++i) {
        const struct content *c = &d.contents[i];
        snprintf(path, sizeof path, "%s/%s%08x.app", dir, subdir ? "00000000/" : "",
                 be32(c->record));
        if (copy_range(dec, c->off, c->size, path)) goto done;
    }
    fprintf(stderr, "3dsdec: installed %s %016llX (%u contents) under %s\n",
            dlc ? "DLC" : "update", (unsigned long long)tid, count, dir);
    if (img->ticket && img->ticket_size) {
        char tdir[4096], tpath[8192];
        snprintf(tdir, sizeof tdir,
                 "%s/nand/00000000000000000000000000000000/dbs/ticket.db", userdir);
        snprintf(tpath, sizeof tpath, "%s/%016llX.%016llX.tik", tdir,
                 (unsigned long long)tid, (unsigned long long)img->ticket_num);
        if (!mkdir_p(tdir)) {
            FILE *tf = fopen(tpath, "wb");
            if (!tf || fwrite(img->ticket, 1, img->ticket_size, tf) != img->ticket_size ||
                fclose(tf)) {
                if (tf) fclose(tf);
                error("cannot write ticket %s", tpath);
            } else {
                fprintf(stderr, "3dsdec: installed ticket %016llX under %s\n",
                        (unsigned long long)tid, tdir);
            }
        }
    }
    result = 0;
done:
    free(d.contents); free(d.tmd); fclose(dec); unlink(tmp);
    return result;
}

/* ---- shared font NAND title installer -------------------------------- */
static void put_le32(uint8_t *p, uint32_t v) { p[0]=v; p[1]=v>>8; p[2]=v>>16; p[3]=v>>24; }
static void put_le64(uint8_t *p, uint64_t v) { for (int i=0;i<8;i++) p[i]=(uint8_t)(v>>(8*i)); }
static void put_be32(uint8_t *p, uint32_t v) { p[0]=v>>24; p[1]=v>>16; p[2]=v>>8; p[3]=v; }
static void put_be64(uint8_t *p, uint64_t v) { for (int i=0;i<8;i++) p[i]=(uint8_t)(v>>(56-8*i)); }

static int read_file_all(const char *path, uint8_t **out, size_t *len) {
    FILE *f=fopen(path,"rb");
    if(!f) return error("cannot open %s: %s",path,strerror(errno));
    struct stat st;
    if(fstat(fileno(f),&st)||st.st_size<=0) { fclose(f); return error("cannot stat %s",path); }
    *len=(size_t)st.st_size; *out=malloc(*len);
    if(!*out) { fclose(f); return error("out of memory"); }
    if(fread(*out,1,*len,f)!=*len) { free(*out); *out=NULL; fclose(f); return error("read failed: %s",path); }
    fclose(f);
    return 0;
}

/* LZ11 with literal blocks only; the core only requires a valid LZ11 stream. */
static uint8_t *lz11_literal(const uint8_t *in, size_t n, size_t *out_len) {
    size_t total=4+n+(n+7)/8;
    uint8_t *out=malloc(total);
    if(!out) return NULL;
    put_le32(out,(uint32_t)((n<<8)|0x11));
    size_t o=4,i=0;
    while(i<n) {
        size_t c=n-i<8?n-i:8;
        out[o++]=0x00;
        memcpy(out+o,in+i,c); o+=c; i+=c;
    }
    *out_len=o;
    return out;
}

static const char FONT_FILE_NAME[]="cbf_std.bcfnt.lz";

static uint8_t *build_romfs(const uint8_t *lz, size_t lz_len, size_t *out_len) {
    const size_t name_len=(sizeof(FONT_FILE_NAME)-1)*2;
    const size_t dir_off=0x28, dir_len=0x18;
    const size_t file_off=dir_off+dir_len;
    const size_t file_len=0x20+name_len;
    const size_t data_off=(file_off+file_len+15)&~(size_t)15;
    size_t total=data_off+lz_len;
    uint8_t *r=calloc(1,total);
    if(!r) return NULL;
    put_le32(r+0x00,0x28);
    put_le32(r+0x04,0); put_le32(r+0x08,0);
    put_le32(r+0x0c,dir_off); put_le32(r+0x10,dir_len);
    put_le32(r+0x14,0); put_le32(r+0x18,0);
    put_le32(r+0x1c,file_off); put_le32(r+0x20,file_len);
    put_le32(r+0x24,data_off);
    uint8_t *d=r+dir_off;
    put_le32(d+0,0); put_le32(d+4,0xffffffff); put_le32(d+8,0xffffffff);
    put_le32(d+12,0); put_le32(d+16,0xffffffff); put_le32(d+20,0);
    uint8_t *fe=r+file_off;
    put_le32(fe+0,0); put_le32(fe+4,0xffffffff);
    put_le64(fe+8,0); put_le64(fe+16,lz_len);
    put_le32(fe+24,0xffffffff); put_le32(fe+28,(uint32_t)name_len);
    for(size_t i=0;i<sizeof(FONT_FILE_NAME)-1;i++) { fe[32+2*i]=(uint8_t)FONT_FILE_NAME[i]; fe[33+2*i]=0; }
    memcpy(r+data_off,lz,lz_len);
    *out_len=total;
    return r;
}

static uint8_t *build_font_ncch(uint64_t tid, const uint8_t *romfs, size_t romfs_len, size_t *out_len) {
    const size_t romfs_off=0x2000;
    size_t total=(romfs_off+romfs_len+0x1ff)&~(size_t)0x1ff;
    uint8_t *a=calloc(1,total);
    if(!a) return NULL;
    memcpy(a+0x100,"NCCH",4);
    put_le32(a+0x104,(uint32_t)(total/0x200));
    put_le64(a+0x118,tid);
    a[0x18d]=0x01;                 /* CFA / data */
    a[0x18f]=0x04;                 /* NoCrypto */
    put_le32(a+0x1b0,8);           /* RomFS at 8*0x200 + 0x1000 */
    put_le32(a+0x1b4,(uint32_t)((romfs_len+0x1000+0x1ff)/0x200));
    memcpy(a+romfs_off,romfs,romfs_len);
    *out_len=total;
    return a;
}

static uint8_t *build_font_tmd(uint64_t tid, const uint8_t *app, size_t app_len, size_t *out_len) {
    const size_t body_off=0x140;
    size_t total=body_off+0x9c4+0x30;
    uint8_t *t=calloc(1,total);
    if(!t) return NULL;
    put_be32(t,0x00010004);        /* RSA-2048 SHA-256, signature not verified */
    uint8_t *b=t+body_off;
    b[0x40]=1;                     /* body version */
    put_be64(b+0x4c,tid);
    put_be32(b+0x54,1);            /* system title */
    b[0x9e]=0; b[0x9f]=1;          /* one content */
    uint8_t *c=t+body_off+0x9c4;
    put_be64(c+8,(uint64_t)app_len);
    unsigned digest_len=0;
    EVP_Digest(app,app_len,c+16,&digest_len,EVP_sha256(),NULL);
    *out_len=total;
    return t;
}

static int write_blob(const char *path, const void *data, size_t len) {
    FILE *f=fopen(path,"wb");
    if(!f) return error("cannot create %s: %s",path,strerror(errno));
    int ok=fwrite(data,1,len,f)==len;
    if(fclose(f)||!ok) { unlink(path); return error("writing %s failed",path); }
    return 0;
}

static int install_font(const char *font_path, const char *userdir) {
    uint8_t *raw=NULL; size_t raw_len=0;
    if(read_file_all(font_path,&raw,&raw_len)) return -1;

    const uint8_t *bcfnt=raw; size_t bcfnt_len=raw_len; int is_lz=0;
    if(bcfnt_len>=4 && !memcmp(bcfnt,"CFNT",4)) {
        is_lz=0;
    } else if(bcfnt_len>0x80 && (!memcmp(bcfnt+0x80,"CFNT",4)||!memcmp(bcfnt+0x80,"CFNU",4))) {
        bcfnt=raw+0x80; bcfnt_len-=0x80;
    } else if(bcfnt_len>0 && bcfnt[0]==0x11) {
        is_lz=1;
    } else {
        free(raw); return error("not a CFNT/shared_font.bin/LZ11 file");
    }

    uint8_t *lz=NULL; size_t lz_len=0;
    if(is_lz) { lz=raw; lz_len=raw_len; }
    else {
        lz=lz11_literal(bcfnt,bcfnt_len,&lz_len);
        if(!lz) { free(raw); return error("out of memory"); }
    }

    size_t romfs_len=0, app_len=0, tmd_len=0;
    uint8_t *romfs=build_romfs(lz,lz_len,&romfs_len);
    if(!romfs) { if(!is_lz) free(lz); free(raw); return error("out of memory"); }

    static const uint64_t tids[2]={UINT64_C(0x0004009B00014002),UINT64_C(0x0004009B00014102)};
    int result=0;
    for(int k=0;k<2 && !result;k++) {
        uint64_t tid=tids[k];
        uint8_t *app=build_font_ncch(tid,romfs,romfs_len,&app_len);
        uint8_t *tmd=app?build_font_tmd(tid,app,app_len,&tmd_len):NULL;
        if(!app||!tmd) { result=error("out of memory"); free(app); free(tmd); break; }
        char dir[4096], path[8192];
        snprintf(dir,sizeof dir,
                 "%s/nand/00000000000000000000000000000000/title/%08x/%08x/content",
                 userdir,(unsigned)(tid>>32),(unsigned)tid);
        if(mkdir_p(dir)) result=-1;
        else {
            snprintf(path,sizeof path,"%s/00000000.tmd",dir);
            if(write_blob(path,tmd,tmd_len)) result=-1;
            else {
                snprintf(path,sizeof path,"%s/00000000.app",dir);
                if(write_blob(path,app,app_len)) result=-1;
                else fprintf(stderr,"3dsdec: installed shared font title %016llX\n",
                             (unsigned long long)tid);
            }
        }
        free(app); free(tmd);
    }
    free(romfs);
    if(!is_lz) free(lz);
    free(raw);
    return result;
}

static void usage(void) {
    fputs("usage:\n  3dsdec --check INPUT\n  3dsdec --decrypt INPUT OUTPUT [--boot9 FILE] [--keys FILE] [--titlekey FILE]\n"
          "Input/output: CIA stays CIA, CCI stays CCI. Existing files are never overwritten.\n"
          "--keys: slot0x2CKeyX/slot0x25KeyX/slot0x18KeyX/slot0x1BKeyX, commonN (normal AES key), fixedSystemKey\n"
          "--seeddb: seeddb.bin for seed-encrypted titles\n"
          "Each entry: name = 32 hex digits. --titlekey: a 16-byte decrypted CIA titlekey.\n"
          " 3dsdec --install-dlc DLC.cia USERDIR [keys...]   # DLC -> emulated SDMC, ticket -> NAND dbs\n"
          " 3dsdec --install-update UPDATE.cia USERDIR [keys...] # update -> NAND title\n"
          "Seed crypto and prototype NCCH v1 are not supported. No keys are embedded.\n",stderr);
}
int main(int argc, char **argv) {
    if (argc<3) { usage(); return 2; }
    int check=!strcmp(argv[1],"--check"), dec=!strcmp(argv[1],"--decrypt");
    int install=!strcmp(argv[1],"--install-dlc") || !strcmp(argv[1],"--install-update");
    int install_is_dlc=!strcmp(argv[1],"--install-dlc");
    int font=!strcmp(argv[1],"--install-font");
    if ((!check && !dec && !install && !font) || (check && argc!=3) ||
        ((dec || install) && (argc<4 || argc%2)) || (font && argc!=4)) { usage(); return 2; }
    if (font) return install_font(argv[2],argv[3]) ? 2 : 0;
    struct keys keys={0};
    for (int i=4;(dec || install) && i<argc;i+=2) {
        int r;
        if (!strcmp(argv[i],"--keys")) r=load_keys(argv[i+1],&keys);
        else if (!strcmp(argv[i],"--seeddb")) r=load_seeddb(argv[i+1],&keys);
        else if (!strcmp(argv[i],"--boot9")) r=load_boot9(argv[i+1],&keys);
        else if (!strcmp(argv[i],"--titlekey")) r=load_titlekey(argv[i+1],&keys);
        else { usage(); return 2; }
        if (r) return 2;
    }
    FILE *in=fopen(argv[2],"rb");
    if (!in) { error("cannot open input: %s",strerror(errno)); return 2; }
    struct image img={0}; int result=2;
    if (!parse_image(in,&img)) {
        if (check) { int r=inspect(in,&img,&keys,0); result=r<0 ? 2 : r; }
        else if (install) {
            struct stat st;
            if (stat(argv[3], &st) || !S_ISDIR(st.st_mode)) error("install destination is not a directory");
            else result = install_title(in, &img, &keys, argv[3], install_is_dlc) ? 2 : 0;
        }
        else {
            const char *ext=strrchr(argv[3],'.');
            int wrap=img.cia && ext && (!strcasecmp(ext,".cci") || !strcasecmp(ext,".3ds"));
            result=decrypt_image(in,argv[3],&img,&keys,wrap) ? 2 : 0;
        }
    }
    free(img.contents); free(img.tmd); free(img.ticket); fclose(in); OPENSSL_cleanse(&keys,sizeof keys); return result;
}
