/*
 * mm.c - Explicit free list implementation
 * 
 * This implementation utilizies the explicit free list to keep track
 * of only the free blocks. This is an improvement from the free list
 * since the search for finding a free block is linear to the number of
 * free blocks in the heap, as opposed to all blocks in the heap. When
 * an allocated block is freed, it is put at the front of the free block
 * list, implementing an Last In First Out ordering. When allocating, if a
 * block can be split for better utilization, the first part of the
 * original block becomes allocated and the second part stays free. 
 * This implementation only implements the simple version of realloc.
 * 
 * In a free block, the original first payload byte holds the pointer that
 * points to the next free block, and the previous pointer is found a word
 * after that. Next is 0 when it is the last free block, and prev is 0 when
 * it is the first free block. The root pointer exists within the prologue
 * block.
 *
 * Helper functions used to debug and print block information commented out
 * at bottom. Otherwise, code is heavily commented.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "Goteam",
    /* First member's full name */
    "Alexander Fang",
    /* First member's email address */
    "alexanderfang2019@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Da-Jun Robert Jin",
    /* Second member's email address (leave blank if none) */
    "dajunjin2016@u.northwestern.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/***
 *  Defining constants and macros (from CSAPP textbook)
 */
#define WSIZE		4 	/* Word and header/foot size (bytes) */
#define DSIZE		8	/* Double word size (bytes) */
#define CHUNKSIZE 	(1<<8)	/* Extend heap by this amount (bytes) */

/* Returns max of x and y */
#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc)) //alloc is lowest 3-bits

/* Read and write a word at address p */
#define GET(p)		(*(unsigned int *)(p)) /* casts p into unsigned
						* int and derefs it */
#define PUT(p, val)	(*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) 	(GET(p) & ~0x7) //includes hdr & ptr
#define GET_ALLOC(p)	(GET(p) & 0x1) //leaves first 3 lowest bits alone

/* Given block ptr bp, compute address of its header and footer */
//bp (block pointers) point to first payload byte
#define HDRP(bp) 	((char *)(bp) - WSIZE) //header is word in front
#define FTRP(bp)	((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
			   //adding size of bp brings to next payload,
			   //footer of orig. bp is 2 words before.

/* Given block ptr bp, compute address of next and previous blocks
 * -- can be free or allocated  */
#define NEXT_BLKP(bp)	((char *)(bp) + GET_SIZE((HDRP(bp)))) 
#define PREV_BLKP(bp)	((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
			   //gets size from the footer of previous block
			   //which is 2 words before	


/***
 * New macros necessary for explicit free list
 */

#define NEXT(bp)	(*(char **)(bp))
#define PREV(bp)	(*((char **)(bp + WSIZE))) //HELLO
#define SETNEXT(bp, nextaddr)	(NEXT(bp) = nextaddr)
#define SETPREV(bp, prevaddr)	(PREV(bp) = prevaddr)

/***
 * Constants
 */

#define MIN_BLKSIZE 16

/***
 * Globals
 */

static char *heap_p  = NULL; /* will point to prologue block */

/***
 * Function protoypes
 */

static void *extend_heap(size_t size);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t size);
static void rmv_from_list(void *bp);
static void insert_front_list(void *bp);
//static int mm_check();
//static void block_data(void* bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
	/* Create the initial empty heap */
	if ((heap_p = mem_sbrk(6*WSIZE)) == (void *)-1)
		return -1;
	PUT(heap_p, 0); /* Alignment padding */
	PUT(heap_p + (1*WSIZE), PACK(MIN_BLKSIZE, 1)); /* Prologue header */
	/* Root information stored in prologue block */
	PUT(heap_p + (2*WSIZE), 0); /* Root has no next yet */
	PUT(heap_p + (3*WSIZE), 0); /* No prev */
	PUT(heap_p + (4*WSIZE), PACK(MIN_BLKSIZE, 1)); /* Prologue footer */
	PUT(heap_p + (5*WSIZE), PACK(0, 1)); /* Epilogue header */
	heap_p += DSIZE; /* Now points to prologue footer */

	/************ EXTEND THE EMPTY HEAP ********/
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1;
	/* Root points to first free block (after prologue) */
	SETNEXT(heap_p, NEXT_BLKP(heap_p));

	/* bp at first free block */
	char *bp = NEXT(heap_p);
	SETNEXT(bp, 0); /* no next ptr yet */
	SETPREV(bp, 0); /* no prev ptr */
	//mm_check();
   	return 0; 
}

static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
	
	/* Coalesce if the previous block was free */
	return coalesce(bp);
}

/* Coalesce; returns bp of the free block */
static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	
	if (prev_alloc && next_alloc)
	{
		insert_front_list(bp);
		return bp;
	}

	else if (prev_alloc && !next_alloc)
	{
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		rmv_from_list(NEXT_BLKP(bp));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		insert_front_list(bp);
	}

	else if (!prev_alloc && next_alloc)
	{
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		bp = PREV_BLKP(bp);
		rmv_from_list(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		insert_front_list(bp);
	}

	else
	{
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
			GET_SIZE(HDRP(NEXT_BLKP(bp)));
		rmv_from_list(PREV_BLKP(bp));
		rmv_from_list(NEXT_BLKP(bp));
		bp = PREV_BLKP(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		insert_front_list(bp);
	}
	return bp;
}

static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp)); /* size of free block */

	/* If difference is more at least  minimum block size, split */
	if ((csize - asize) >= MIN_BLKSIZE)
	{
		/* new size changes where next is */
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		
		/* new free block pointer */
		char *nfbp = NEXT_BLKP(bp);
		if (PREV(bp) && NEXT(bp))
		/* if it wasn't the first or last block */
		{
			char *orig_next = NEXT(bp);
			char *orig_prev = PREV(bp);
			/* Give new free block the old next and prev */
			SETNEXT(nfbp, orig_next);
			SETPREV(nfbp, orig_prev);
			
			/* Old next and prev point to new block */
			SETNEXT(orig_prev, nfbp);
			SETPREV(orig_next, nfbp);
		}	
		/* if first free block */
		else if (!(PREV(bp)) && NEXT(bp))
		{
			char *orig_next = NEXT(bp);
			SETNEXT(heap_p, nfbp);
			SETPREV(nfbp, 0);
			SETNEXT(nfbp, orig_next);
			SETPREV(orig_next, nfbp);
		}
		/* if last free block */
		else if (PREV(bp) && !(NEXT(bp)))
		{
			char *orig_prev = PREV(bp);
			SETNEXT(orig_prev, nfbp);
			SETNEXT(nfbp, 0);
			SETPREV(nfbp, orig_prev);
		}
		else /* if it's the only block */
		{
			SETNEXT(heap_p, nfbp);
			SETNEXT(nfbp, 0);
			SETPREV(nfbp, 0);
		}
		/* new free block pointer allocated bit and size */
		PUT(HDRP(nfbp), PACK(csize-asize, 0));
		PUT(FTRP(nfbp), PACK(csize-asize, 0));
	}
	/* no splitting */
	else
	{	
		rmv_from_list(bp);
		PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
	}
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 *     Returns a pointer to first payload byte
  */
void *mm_malloc(size_t size)
{
	size_t adjsize; /* Adjusted block size */
	size_t extsize; /* Amount to extend heap if no fit */
	char *bp;	

	/* Ignore spurious requests */
	if (size == 0)
	{
		return NULL;
	}
	
	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		adjsize = 2*DSIZE;
	else
		adjsize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

	/* Search the free list for a fit */
	if ((bp = find_fit(adjsize)) != NULL)
	{
		place(bp, adjsize);
		return bp;
		/* returns pointer to allocated block */
	}
	
	extsize = MAX(adjsize, CHUNKSIZE);
	/* need more than chunk? */
	if ((bp = extend_heap(extsize/WSIZE)) == NULL)
	{
		printf("extend_heap failed \n");
		return NULL;
	}
	place(bp, adjsize);
	return bp;
}

static void *find_fit(size_t asize)
{
	char *bp;
	int done = 0;
	/* start at first free block, */
	if (!(NEXT(heap_p)))
	{
		return NULL;
	}
	else
	{
		bp = NEXT(heap_p);
	}
	do
	{
		if (asize <= GET_SIZE(HDRP(bp)))
		{
			return bp;
		}
		else if (NEXT(bp) != 0)
		{
			bp = NEXT(bp);
		}
		else
		{
			done = 1;
		}
	} while (done != 1);
	return NULL;
}

/*
 * mm_free - Freeing with LIFO policy
 */
void mm_free(void *bp)
{

	/* size should be double word aligned */
	size_t size = GET_SIZE(HDRP(bp));	
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
	size_t adjsize;

	adjsize = ALIGN(size);
    newptr = mm_malloc(size);

    if (newptr == NULL)
      return NULL;

    copySize = GET_SIZE(HDRP(oldptr));

    if (adjsize < copySize)
      copySize = adjsize;

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
	
}

static void rmv_from_list(void *bp)
{
	if (PREV(bp) && NEXT(bp))
	{
                char *orig_prev = PREV(bp);
                char *orig_next = NEXT(bp);
                SETNEXT(orig_prev, orig_next);
                SETPREV(orig_next, orig_prev);
        }

        else if (!(PREV(bp)) && NEXT(bp))
        {
                char *orig_next = NEXT(bp);
                SETNEXT(heap_p, orig_next);
                SETPREV(orig_next, 0);
        }

        else if (PREV(bp) && !(NEXT(bp)))
        {
                char *orig_prev = PREV(bp);
                SETNEXT(orig_prev, 0);
        }

        else
        {
                SETNEXT(heap_p, 0);
        }
		
}

/* inserts a free block at the front of the list -- checks
 * if there's nothing already at the front of the list! */
static void insert_front_list(void *bp)
{
	if (NEXT(heap_p))
	{
		char *orig_first = NEXT(heap_p);
		SETNEXT(bp, orig_first);
		SETPREV(orig_first, bp);
	}
	else
	{
		SETNEXT(bp, 0);
	}
	SETNEXT(heap_p, bp);
	SETPREV(bp, 0);
}

/*
static int mm_check(void)
{
//	printf("-- mm_check \n");
	int success = 1;
	size_t heapsize = mem_heapsize();
	void *mem_lo = mem_heap_lo();
	void *mem_hi = mem_heap_hi();
	void *bp;

	for (bp = heap_p; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
	{
		if (GET(HDRP(bp)) != GET(FTRP(bp)))
		{
			printf("HEADER AND FOOTERS NOT EQUAL \n");
			printf("Header: %p \n", (void *)HDRP(bp));
			printf("Footer: %p \n", (void *)FTRP(bp));
			success = 0;
		}
		if (((int)bp % DSIZE) != 0)
		{
			printf("BLOCK NOT ALIGNED PROPERLY \n");
			printf("%p", bp);
			success = 0;
		}
		if (GET_ALLOC(HDRP(bp)) == 0 &&
			 GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0)
		{
			printf("TWO ADJACENT FREE BLOCKS");
			success = 0;
		}
		if ((GET_ALLOC(HDRP(bp))) == 0)  //if it's a free block
		{
			if ((NEXT(bp) != 0) &&
				 (int *)NEXT(bp) < (int *) mem_lo)
			{
				printf("bp's NEXT ADDRESS TOO LOW \n");
				success = 0;
			}
			if ((NEXT(bp) != 0) &&
				(int *) NEXT(bp) > (int *) mem_hi)
			{
				printf("bp's NEXT ADDRESS TOO HIGH \n");
				success = 0;
			}
			if ((PREV(bp) != 0) &&
				 (int *)PREV(bp) < (int *) mem_lo)
			{
				printf("bp's PREV ADDRESS TOO LOW %p,
					 %p\n", bp, PREV(bp));
				success = 0;
			}
			if ((PREV(bp) != 0) &&
				 (int *)PREV(bp) > (int *) mem_hi)
			{
				printf("bp's PREV ADDRESS TOO HIGH \n");
				success = 0;
			}
		}	
	}

	if (!success)
	{
		bp = heap_p;
	        printf("HEAP STARTS AT %p \n", (void *)heap_p);
	        printf("HEAP SIZE: %zu bytes \n", heapsize);
	        printf("mem_lo = %p \n", mem_lo);
	        printf("mem_hi = %p \n", mem_hi);
	
	        printf("BLK DATA OF heap_p: \n");
	        printf("heap_p points to: %p \n", NEXT(heap_p));
	        block_data(heap_p);
	        printf("\n");
		
		for (bp = heap_p; GET_SIZE(HDRP(bp)) > 0;
						 bp = NEXT_BLKP(bp))
		{
			block_data(bp);
		}
	}
	return success;
	printf("@@@@@@@@@@@ \n");
}

static void block_data(void *bp)
{
	printf("-- Block data \n");
	int hsize, halloc, fsize, falloc;
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));
	if (hsize == 0)
	{
		printf("EPILOGUE BLOCK");
	}
	if (halloc)
	{
		printf("ALLOCATED BLOCK: %p \n", (void *)bp);
		printf("Size: %i bytes \n", hsize);
		
	}
	else
	{
		printf("FREE BLOCK: %p \n", (void *)bp);
		printf("Size: %i bytes \n", hsize);
		printf("Next: %p \n", (void *)(NEXT(bp)));
		printf("Prev: %p \n", (void *)(PREV(bp)));
	}
	printf("@@@@@@@@@@ \n");
}
*/







