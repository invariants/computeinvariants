CC=gcc
CFLAGS=-I. -std=c99 -O3
DEPS = uthash.h lookup.h
OBJ = computeinvariants.o

.PHONY: computeinvariants %.o clean 

%.o: %.c $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

computeinvariants: $(OBJ)
	gcc -o $@ $^ $(CFLAGS)

clean:
	rm -f *.o core
