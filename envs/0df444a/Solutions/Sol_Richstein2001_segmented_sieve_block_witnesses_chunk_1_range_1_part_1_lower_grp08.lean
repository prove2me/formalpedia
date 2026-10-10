-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp08
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T02:21:36.894335+00:00
-- url     : https://prove2.me/submissions/13b104d6-19bc-41b4-88d9-7e64d30c60e5

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0351
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0352
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0353
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0354
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0355
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0356
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0357
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0358
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0359
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0360
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0361
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0362
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0363
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0364
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0365
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0366
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0367
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0368
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0369
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0370
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0371
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0372
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0373
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0374
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0375
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0376
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0377
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0378
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0379
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0380
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0381
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0382
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0383
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0384
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0385
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0386
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0387
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0388
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0389
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0390
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0391
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0392
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0393
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0394
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0395
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0396
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0397
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0398
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0399
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0400

/-! Link reduction: `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp08` (blocks [50003500, 50004000)) from the 50 chunks `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0351` .. `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0400`, which tile that range end to end; a balanced case split on b selects the chunk. -/

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50003500 <= b) (hhi : b < 50004000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  rcases Nat.lt_or_ge b 50003750 with hc25 | hc25
  · rcases Nat.lt_or_ge b 50003620 with hc12 | hc12
    · rcases Nat.lt_or_ge b 50003560 with hc6 | hc6
      · rcases Nat.lt_or_ge b 50003530 with hc3 | hc3
        · rcases Nat.lt_or_ge b 50003510 with hc1 | hc1
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0351 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003520 with hc2 | hc2
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0352 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0353 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50003540 with hc4 | hc4
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0354 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003550 with hc5 | hc5
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0355 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0356 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50003590 with hc9 | hc9
        · rcases Nat.lt_or_ge b 50003570 with hc7 | hc7
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0357 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003580 with hc8 | hc8
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0358 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0359 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50003600 with hc10 | hc10
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0360 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003610 with hc11 | hc11
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0361 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0362 b hb (by omega) (by omega)
    · rcases Nat.lt_or_ge b 50003680 with hc18 | hc18
      · rcases Nat.lt_or_ge b 50003650 with hc15 | hc15
        · rcases Nat.lt_or_ge b 50003630 with hc13 | hc13
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0363 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003640 with hc14 | hc14
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0364 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0365 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50003660 with hc16 | hc16
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0366 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003670 with hc17 | hc17
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0367 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0368 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50003710 with hc21 | hc21
        · rcases Nat.lt_or_ge b 50003690 with hc19 | hc19
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0369 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003700 with hc20 | hc20
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0370 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0371 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50003730 with hc23 | hc23
          · rcases Nat.lt_or_ge b 50003720 with hc22 | hc22
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0372 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0373 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003740 with hc24 | hc24
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0374 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0375 b hb (by omega) (by omega)
  · rcases Nat.lt_or_ge b 50003870 with hc37 | hc37
    · rcases Nat.lt_or_ge b 50003810 with hc31 | hc31
      · rcases Nat.lt_or_ge b 50003780 with hc28 | hc28
        · rcases Nat.lt_or_ge b 50003760 with hc26 | hc26
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0376 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003770 with hc27 | hc27
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0377 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0378 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50003790 with hc29 | hc29
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0379 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003800 with hc30 | hc30
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0380 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0381 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50003840 with hc34 | hc34
        · rcases Nat.lt_or_ge b 50003820 with hc32 | hc32
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0382 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003830 with hc33 | hc33
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0383 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0384 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50003850 with hc35 | hc35
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0385 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003860 with hc36 | hc36
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0386 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0387 b hb (by omega) (by omega)
    · rcases Nat.lt_or_ge b 50003930 with hc43 | hc43
      · rcases Nat.lt_or_ge b 50003900 with hc40 | hc40
        · rcases Nat.lt_or_ge b 50003880 with hc38 | hc38
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0388 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003890 with hc39 | hc39
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0389 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0390 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50003910 with hc41 | hc41
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0391 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003920 with hc42 | hc42
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0392 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0393 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50003960 with hc46 | hc46
        · rcases Nat.lt_or_ge b 50003940 with hc44 | hc44
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0394 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003950 with hc45 | hc45
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0395 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0396 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50003980 with hc48 | hc48
          · rcases Nat.lt_or_ge b 50003970 with hc47 | hc47
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0397 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0398 b hb (by omega) (by omega)
          · rcases Nat.lt_or_ge b 50003990 with hc49 | hc49
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0399 b hb (by omega) (by omega)
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0400 b hb (by omega) (by omega)
