CC      = /home/lcdyk/sdl2_xbuild/bin/ac13-gcc
HOST_CC ?= cc
CFLAGS  ?= -O2 -Wall -Wextra
LDLIBS  ?= -lcrypto

3dsdec: 3dsdec.c
	$(CC) $(CFLAGS) -o $@ $< $(LDLIBS)

3dsdec-host: 3dsdec.c
	$(HOST_CC) $(CFLAGS) -o $@ $< $(LDLIBS)

test: 3dsdec-host
	python3 tests/selftest.py ./3dsdec-host

clean:
	rm -f 3dsdec 3dsdec-host

.PHONY: clean test
