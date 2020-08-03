/*
***********************IMPLEMENTATION*************************

Heap structure has segregated list that contains only freed block
The number of segregated lists is 13. It is odd number because we have to follow 8byte alignment.
The lists is differ from size. Size start 2^4. range is 2^n ~ (2^n+1)-1
At the start and end of heap, heap has prologues and epilogues of each lists.
List exists between prologues and epilogues of each lists.

Block structure has header and footer.
header and footer has block size and free bit.
free bit is 1 when freed, 0 when allocated.
free block has PRED and NEXT pointer because segregated list is doubly linked list.

Segregated lists
first, it has prologue and epilogue.
when we get freed block, 
we put block to list between prologue and epilogue according to the size of freed block.
prologue has PRED, SUCC, footer
epilogue had header, PRED, SUCC. 
So prologue and epilogue is 3word size.

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

/* single word (4) or double word (8) alignment */

#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//Basic constants and macros
#define WSIZE	4 //Word and header/footer size (bytes)
#define DSIZE	8 //Double word size (bytes)
#define CHUNKSIZE	(1<<12) //Extend heap by this amount (bytes)

#define MAX(x, y)	((x) > (y)? (x) : (y))

//Pack a size and allocated bit into a word
#define PACK(size, alloc)	((size) | (alloc))

//Read and write a word at address p
#define GET(p)	(*(unsigned int *)(p))
#define PUT(p, val)	(*(unsigned int *)(p) = (val))

//Read the size and allocated fields from address p
#define GET_SIZE(p)	(GET(p) & ~0x7)
#define GET_ALLOC(p)	(GET(p) & 0x1)

//Given block ptr bp, compute address of its header and footer
#define HDRP(bp)	((char *)(bp) - WSIZE)
#define FTRP(bp)	((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp)	((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)	((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

//---------------------------------------------------------------------------------
// use alloc bit as free bit
// alloc = 0, free = 1
#define GET_FREE_BIT(p) GET_ALLOC(p)
#define GET_PREV_FTRP(bp) (size_t *)((char *)(bp) - DSIZE)
#define GET_NEXT_HDRP(bp) (size_t *)((char *)(bp) + GET_SIZE(HDRP(bp)) - WSIZE)

#define MIN_BLOCK_SIZE 16

//prev and next of free block
#define PREVP(fbp) ((size_t **)(fbp))
#define NEXTP(fbp) ((size_t **)((char *)(fbp) + WSIZE))

#define SEGLIST_COUNT 13

#define PROLOG_SIZE (SEGLIST_COUNT * 3 * WSIZE)
#define EPILOG_SIZE (PROLOG_SIZE)

static size_t *ptr_heap, heap_size;

#define pro_start() (ptr_heap)
#define pro_block(num) (pro_start() + (num) * 3)
#define blk_start(num) (*NEXTP(pro_block(num)))
#define epil_start() ((size_t *)((char *)(ptr_heap) + ((heap_size) - EPILOG_SIZE)))
#define new_size(size) ALIGN(size) + DSIZE
#define blk_end() (size_t *)((char *)(epil_start() - 1) - GET_SIZE(epil_start() - 1) + DSIZE)


//according to the size of freed block, get the index of segregated list to put freed block 
static int get_seglist_number(size_t size) {
        //take log of size(result is r-1)
        int r;
        frexp((double)size, &r);
        //num is index of list
        int num = (int)(r-1) - 4;
        if(num < 0) num = 0;
        if(num >= SEGLIST_COUNT) num = SEGLIST_COUNT - 1;
        return num;
}

//insert new freed block to free list
static void insert_to_free_list(size_t *bp){

    	int list_num = get_seglist_number(GET_SIZE(HDRP(bp)));

    	size_t *prev = pro_block(list_num);
    	size_t *next = blk_start(list_num);

    	*PREVP(bp) = prev;
    	*NEXTP(bp) = next;

    	*PREVP(next) = bp;
        *NEXTP(prev) = bp;

}

//remove unfreed block from free list
static void remove_from_free_list(size_t *bp){

    	size_t *prev = *PREVP(bp);
    	size_t *next = *NEXTP(bp);

    	*PREVP(next) = prev;
	*NEXTP(prev) = next;
}   



static void *find_fit(size_t size, int num){
	
	if(num >= SEGLIST_COUNT) return NULL; 

	while(num < SEGLIST_COUNT)
	{	
		int current_blk = blk_start(num);		
		while(*HDRP(current_blk))
		{
			if(GET_FREE_BIT(HDRP(current_blk)) && (GET_SIZE(HDRP(current_blk)) >= size)) 
				return current_blk; //we do working in this block
			current_blk = *NEXTP(current_blk); //if we doens't find block, move to next seglist
		}
		num++;
	}	
}



// place the block(header, footer)
static void place(size_t *addr, size_t size, int is_free){

	PUT(HDRP(addr), PACK(size, is_free));
    	PUT(FTRP(addr), PACK(size, is_free));
}


// expand heap size and update epilogues
static void expand_heap(size_t size){

        size_t *old_epil = epil_start();
        size_t *new_epil = (size_t *)((char *)mem_sbrk(size) + size - EPILOG_SIZE);

        heap_size += size;
        //move epilog to the end of heap
        memmove(new_epil, old_epil, EPILOG_SIZE);

        //replace SUCC of each epilogue
        size_t *epils = new_epil + 1;
        for(int i=0; i<SEGLIST_COUNT; i++)
        {
                *NEXTP(*PREVP(epils)) = epils;
                epils += 3;
        }
}


// initailize heap 
int mm_init(void){
        heap_size = PROLOG_SIZE + EPILOG_SIZE;
        ptr_heap = mem_sbrk(heap_size);

        // initialize prologs and  epilogs of each seglist
        int i;
        size_t *p = ptr_heap;
        size_t *pro = pro_start();
	size_t *epi = epil_start() + 1;

        // init prolog list
        for(i=0; i<SEGLIST_COUNT; i++)
        {
                *p = 0; p++; 
                *p = (size_t)(epi); p++;
                *p = 0; p++;
                epi += 3;
        }
        // init epilog list
        for(i=0; i<SEGLIST_COUNT; i++)
        {
                *p = 0; p++;
                *p = (size_t)(pro); p++;
                *p = 0; p++;
                pro += 3;
        }

        return 0;
}


void *mm_malloc(size_t size){
    	
	if(size == 0) return NULL;

    	size_t asize = new_size(size);
    	size_t *bp;

   	if((bp = find_fit(asize, get_seglist_number(asize)))) 
	{
        	remove_from_free_list(bp);

		size_t block_size = GET_SIZE(HDRP(bp));
        	if(block_size - asize >= MIN_BLOCK_SIZE) //block is big, need to spilt 
		{
            		place(bp, asize, 0);
            		size_t * remain_size = NEXT_BLKP(bp);
            		place(remain_size, block_size - asize, 1);
            		insert_to_free_list(remain_size);
        	} 
		else place(bp, block_size, 0); //not spilt
    	} 
	else //size is too big, move to next list 
	{
        	if(GET_FREE_BIT(epil_start() - 1)) 
		{
            		bp = blk_end();
            		remove_from_free_list(bp);
            		size_t last_blk_size = GET_SIZE(HDRP(bp));
            		expand_heap(asize - last_blk_size);
        	} 
		else 	
		{
            		bp = epil_start() + 1;
            		expand_heap(asize);
        	}
        	place(bp, asize, 0);
    	}

    	return bp;
}

// our free function: with coalescing
void mm_free(void *ptr){

    	size_t *bp = (size_t *)ptr;

    	size_t size = GET_SIZE(HDRP(bp));

    	place(ptr, size, 1);

    	size_t prev_free = GET_FREE_BIT(GET_PREV_FTRP(bp));
    	size_t next_free = GET_FREE_BIT(GET_NEXT_HDRP(bp));

    	size_t *prev_block = PREV_BLKP(bp);
    	size_t *next_block = NEXT_BLKP(bp);

    	// coalesce blocks
    	if(prev_free && next_free) 
	{
        	remove_from_free_list(prev_block);
        	remove_from_free_list(next_block);
        	size += GET_SIZE(GET_PREV_FTRP(bp)) + GET_SIZE(GET_NEXT_HDRP(bp));
        	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1));
        	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
        	bp = PREV_BLKP(bp);
    	} 
	else if(!prev_free && next_free) 
	{ 
        	remove_from_free_list(next_block);
        	size +=  GET_SIZE(GET_NEXT_HDRP(bp));
        	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1));
        	PUT(HDRP(bp), PACK(size, 1));
    	} 
	else if(prev_free && !next_free) 
	{
        	remove_from_free_list(prev_block);
        	size += GET_SIZE(GET_PREV_FTRP(bp));
        	PUT(FTRP(bp), PACK(size, 1));
        	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
        	bp = PREV_BLKP(bp);
    	}
    	insert_to_free_list(bp);
}

// our realloc function: try utilizing next block & autonomous heap expansion
void *mm_realloc(void *ptr, size_t size){
    	// if ptr == NULL, malloc
    	if(!ptr) return mm_malloc(size);
    
    	// if size == 0, free
    	if(!size) 
 	{
        	mm_free(ptr);
        	return NULL;
    	}

    	size_t asize = new_size(size);
    	size_t cur_size = GET_SIZE(HDRP(ptr));

    	void * oldptr = ptr;

    	// first check whether surrounding free blocks exist

    	// no utilizing with prev block.. it hinders overall utilization rate
    	size_t prev_free = 0;//GET_FREE_BIT(GET_PREV_FTRP(ptr));
    	size_t next_free = GET_FREE_BIT(GET_NEXT_HDRP(ptr));

    	size_t prev_size = GET_SIZE(GET_PREV_FTRP(ptr));
    	size_t next_size = GET_SIZE(GET_NEXT_HDRP(ptr));

    	size_t *prev_block = PREV_BLKP(ptr);
    	size_t *next_block = NEXT_BLKP(ptr);
    	size_t *new_block;
    	size_t total_size, new_block_size;

    	// check is expandable block..
    	size_t is_last = blk_end() == ptr;
    
    	// data size to copy/move
    	size_t data_size = (asize < cur_size ? asize : cur_size) - DSIZE;
    	if(prev_free && next_free && (prev_size + cur_size + next_size >= asize || is_last)) 
	{
        	// utilize both side
        	total_size = prev_size + cur_size + next_size;
        	remove_from_free_list(prev_block);
        	remove_from_free_list(next_block);
        	ptr = memmove(prev_block, ptr, data_size);        
    	} 
	else if(!prev_free && next_free && (cur_size + next_size >= asize || is_last)) 
	{
        	// utilize next side 
        	total_size = cur_size + next_size;
        	remove_from_free_list(next_block);
    	} 
	else if(prev_free && !next_free && (prev_size + cur_size >= asize || is_last)) 
	{
        	// utilize prev side
        	total_size = prev_size + cur_size;
        	remove_from_free_list(prev_block);
        	ptr = memmove(prev_block, ptr, data_size);        
	} 
	else if(!prev_free && !next_free && (cur_size >= asize || is_last)) 	
	{
        	total_size = cur_size;
    	} 
	else 	
	{
        	// in this case, we will use simply malloc & free.. 
        	size_t *temp = mm_malloc(asize);
        	memcpy(temp, ptr, data_size);
        	mm_free(ptr);

        	return temp;
    	}


    	if(total_size < asize) 
	{
        	// expand the heap
        	expand_heap(asize - total_size);

        	place(ptr, asize, 0);
        	new_block = NULL;
    	} 
	else 
	{
        	new_block_size = total_size - asize;

        	// determine to split
        	if(new_block_size >= MIN_BLOCK_SIZE) 
		{
            		// split
            		// set header & footer
            		place(ptr, asize, 0);

            		// set new block
            		new_block = FTRP(ptr) + 2;
            		place(new_block, new_block_size, 1);
            		insert_to_free_list(new_block);
    	    	} 
		else 
		{
            		// non-split
            		place(ptr, total_size, 0);
            		new_block = NULL;
        	}
    	}


    	return ptr;
}

//check error
int mm_check(void){
        size_t *cur_block;
        cur_block = (pro_start() + (SEGLIST_COUNT * 3 + 1)); //first block of each list

        while(*HDRP(cur_block)) //from start to end of list
        {
                if(*HDRP(cur_block) != *FTRP(cur_block))
                        printf("header and footer are differnt");
                if(GET_FREE_BIT(HDRP(cur_block)))
                {
                        if(GET_FREE_BIT(GET_PREV_FTRP(cur_block)))
                                printf("prev coalescing error");
                        if(GET_FREE_BIT(GET_NEXT_HDRP(cur_block)))
                                printf("next coalescing error");
                }
                cur_block = NEXT_BLKP(cur_block);
        }

        for(int num=0; num<SEGLIST_COUNT; num++) //from start to end of list
        {
                cur_block = blk_start(num); // start of each list
                while(*HDRP(cur_block))
                {
                        if(GET_FREE_BIT(HDRP(cur_block)) == 0)
                        	printf("allocated block in free list");
                        cur_block = *NEXTP(cur_block);
                }
        }
        return 0;
}
