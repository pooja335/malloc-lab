/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team awesome",
    /* First member's full name */
    "Pooja Saxena",
    /* First member's email address */
    "poojasaxena2016@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Brian Capella",
    /* Second member's email address (leave blank if none) */
    "briancapella2017@u.northwestern.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE		4
#define DSIZE		8
#define CHUNKSIZE	(1<<12)

static void *heap_listp;
static void *freelist_ptr;	

/* read and write values to memory */
#define GET(p)		(*(unsigned int *)(p))
#define SET(p, val)	(*(unsigned *)(p) = (val))

/* given a block pointer, give address of header and footer */
#define HEADER(bp)	((char *)(bp) - WSIZE)
#define	FOOTER(bp)	((char *)(bp) + BLOCKSIZE(HEADER(bp)) - DSIZE)

/* given a header pointer, return true if block is free or allocated*/
#define ISFREE(hp)	(!(GET(hp) & 0x1))
#define	ISALLOC(hp)	(GET(hp) & 0x1)

/* given a header pointer, returns size of block including header and footer */
#define BLOCKSIZE(hp)	(GET(hp) & ~0x7)

/* given a block pointer, gives address of next block pointer */
#define NEXT(bp)		((char *)(bp) + BLOCKSIZE((char *)(bp) - WSIZE))
#define PREV(bp)        ((char *)(bp) - BLOCKSIZE((char *)(bp) - DSIZE))

/* assembles header and footer */
#define PACK(size, alloc)	((size) | (alloc))

#define MAX(x, y)	(((x) > (y)) ? (x) : (y))

/* helper functions */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void mm_check(void);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
	printf("function: mm_init\n");
	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {
		return -1;
	}
	SET(heap_listp, 0);
	SET(heap_listp + WSIZE, PACK(DSIZE, 1));
	SET(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
	SET(heap_listp + (3*WSIZE), PACK(0, 1));
	heap_listp += (2*WSIZE);
	// freelist_ptr = NULL;
	// printf("mem_heap_lo: %d\n", (unsigned int)(mem_heap_lo()));
	// printf("mem_heap_hi: %d\n", (unsigned int)(mem_heap_hi()));
	if (extend_heap(ALIGN(CHUNKSIZE/WSIZE)) == NULL) {
		return -1;
	}
	return 0;
}

/* function to extend the heap */
static void *extend_heap(size_t words) 
{
	printf("function: extend_heap\n");
	char *bp;
	size_t size;

	/* Allocate an even number of words for alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1) {
		return NULL;
	}
	
	/* Initialize free block header and footer and epilogue header */
	SET(HEADER(bp), PACK(size, 0));
	SET(FOOTER(bp), PACK(size, 0));
	SET(HEADER(NEXT(bp)), PACK(0, 1));

	/* Coalesce if needed */
	return coalesce(bp);	

}


/* fuction used to coalesce */
static void *coalesce(void *bp) 
{
	printf("function: coalesce\n");
	// printf("bp: %d\n", (unsigned int)(bp));
	// printf("bp next: %d\n", (unsigned int)(NEXT(bp)));
	// printf("mem_heap_lo: %d\n", (unsigned int)(mem_heap_lo()));
	// printf("mem_heap_hi: %d\n", (unsigned int)(mem_heap_hi()));
	size_t prev_alloc = ISALLOC(FOOTER(PREV(bp)));
	size_t next_alloc = ISALLOC(HEADER(NEXT(bp)));
	size_t size = BLOCKSIZE(HEADER(bp));

	if (prev_alloc && next_alloc) {
		return bp;
	}

	else if (prev_alloc && !next_alloc) {
		size += BLOCKSIZE(HEADER(NEXT(bp)));
		SET(HEADER(bp), PACK(size, 0));
		SET(FOOTER(bp), PACK(size, 0));
	}

	else if (!prev_alloc && next_alloc) {
		size += BLOCKSIZE(HEADER(PREV(bp)));
		SET(FOOTER(bp), PACK(size, 0));
		SET(HEADER(PREV(bp)), PACK(size, 0));
		bp = PREV(bp);
	}

	else {
		size += BLOCKSIZE(HEADER(PREV(bp))) + BLOCKSIZE(FOOTER(NEXT(bp)));
		SET(HEADER(PREV(bp)), PACK(size, 0));
		SET(FOOTER(NEXT(bp)), PACK(size, 0));
		bp = PREV(bp);
	}
	return bp;
}


/* function used to search free list for fit */
static void *find_fit(size_t asize)
{
	printf("function: find_fit\n");
	void *bp;
	for (bp = heap_listp; BLOCKSIZE(HEADER(bp)) > 0; bp = NEXT(bp)) {
		// printf("find_fit");
		// printf("bp: %d\n", (unsigned int)(bp));
		// printf("bp next: %d\n", (unsigned int)(NEXT(bp)));
		// printf("mem_heap_lo: %d\n", (unsigned int)(mem_heap_lo()));
		// printf("mem_heap_hi: %d\n", (unsigned int)(mem_heap_hi()));
		if (!ISALLOC(HEADER(bp)) && (asize <= BLOCKSIZE(HEADER(bp)))) {
			return bp;
		}
	}
	return NULL;
}

/* function used to place requested block at beginning of free block */
static void place(void *bp, size_t asize) 
{
	printf("function: place\n");
	size_t csize = BLOCKSIZE(HEADER(bp));
	if ((csize - asize) >= (2*DSIZE)) {
		SET(HEADER(bp), PACK(asize, 1));
		SET(FOOTER(bp),	PACK(asize, 1));
		bp = NEXT(bp);
		SET(HEADER(bp),	PACK((csize - asize), 0));
		SET(FOOTER(bp), PACK((csize - asize), 0));	
	}	
	else {
		SET(HEADER(bp), PACK(csize, 1));
		SET(FOOTER(bp), PACK(csize, 1));
	}
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
/* 
	int newsize = ALIGN(size + SIZE_T_SIZE);
  	void *p = mem_sbrk(newsize);
  	if (p == (void *)-1)
		return NULL;
 	else {
  	     *(size_t *)p = size;
  	     return (void *)((char *)p + SIZE_T_SIZE);
  	}
  */
	printf("function: mm_malloc\n");
	size_t asize;
	size_t extendsize;
	char *bp;
	
	if (size == 0) {
		return NULL;
	}
	if (size <= 2*WSIZE) {
		asize = 2*DSIZE;
	}
	else {
		asize = DSIZE*((size + DSIZE + (DSIZE-1)) / DSIZE);
	}
	asize = ALIGN(asize);

	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
	}

	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(ALIGN(extendsize/WSIZE))) == NULL) {return NULL;}
	place(bp, asize);
	return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *p)
{
	printf("function: mm_free\n");
	size_t size = BLOCKSIZE(HEADER(p));

	SET(HEADER(p), PACK(size, 0));
	SET(FOOTER(p), PACK(size, 0));
	coalesce(p);

}





/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *p, size_t size)
{
	printf("function: mm_realloc\n");
    void *oldptr = p;
    void *newptr;
    size_t oldSize;
    
    if (p == NULL) {
    return mm_malloc(size);
    }
    if (size == 0) {
    mm_free(p);
    return NULL;
    }

    // malloc a new pointer
    newptr = mm_malloc(size);
    if (newptr == NULL) {
      return NULL;
    }
    
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    oldSize = BLOCKSIZE(HEADER(p));
    if (size < oldSize) {
      oldSize = size;
    }
    memcpy(newptr, oldptr, oldSize);
    mm_free(oldptr);
    return newptr;
}




/*
 * mm_check - Checks the heap, scans for consistency
 * Is every block in the free list marked as free? CHECK
 * Are there any contiguous free blocks that somehow escaped coalescing? CHECK 
 * Is every free block actually in the free list? CHECK
 * Do the pointers in the free list point to valid free blocks? CHECK
 * Do any allocated blocks overlap? CHECK
 * Do the pointers in a heap block point to valid heap addresses? CHECK
 */
void mm_check(void)
{
	printf("function: mm_check\n");
    	/* check if all pointers point to valid heap address (in bounds) */
    	void *current = heap_listp;
	while (current != NULL) {
		if (current < mem_heap_lo() || current > mem_heap_hi()) {
			printf("ERROR1\n");
			break;
    		}
		current = NEXT(current);
	} 	

	/* check if every block in the free list marked as free */
	current = freelist_ptr;
	while ((void *)(GET(current)) != NULL) {
		if (ISALLOC(HEADER(current))) {
			printf("ERROR2\n");
			break;
		}
		current = NEXT(current);
	}

	/* check if all contiguous free blocks are coalesced */
	current = heap_listp;
	int flag = 0;
        while (current != NULL) {
		flag = ISFREE(HEADER(current));
		if (flag && ISFREE(HEADER(NEXT(current)))) {
			printf("ERROR3\n");
			break;
		}
                current = NEXT(current);
        }

	/* check if every free block is actually in the free list */
	current = heap_listp;
	void *current_free;
        while (current != NULL) {
		flag = 1;
                if (ISFREE(HEADER(current))) {
			current_free = freelist_ptr;
			while ((void *)(GET(current_free)) != NULL) {
				if (GET(current) == GET(current_free)) {
					flag = 0;
					break;
				}
				current_free = NEXT(current_free);
			}
			if (flag) {
				printf("ERROR4\n");
				break;
			}
                }
                current = NEXT(current);
        }

	/* check if every element in free list is in the heap */
        current_free = freelist_ptr;
        void *current_heap;
        while ((void *)(GET(current_free)) != NULL) {
		flag = 1;
		current_heap = heap_listp;
		while (current_heap != NULL) {
			if (GET(current_heap) == GET(current_free)) {
                                flag = 0;
                                break;
                        }
			current_heap = NEXT(current_heap);
		}
		if (flag) {
			printf("ERROR5\n");
			break;
		}
		current_free = NEXT(current_free);
	}

	/* check that no blocks overlap */
	current = heap_listp;
	while (current != NULL) {
		if (FOOTER(current) >= HEADER(NEXT(current))) {
			printf("ERROR6\n");
			break;
		}
		current = NEXT(current);
	}	
}










