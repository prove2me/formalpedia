-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:26:03.102283+00:00
-- url     : https://prove2.me/submissions/5c58ae5c-f911-4321-ac06-719d648cd8ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_5_sub_290
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_5_sub_291
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_5_sub_292
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_5_sub_293
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_5_sub_294
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_5_sub_295
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_5_sub_296
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_5_sub_297
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_5_sub_298
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_5_sub_299

theorem solution (b : Nat) (hb : Nat.lt b 400000001) (hlo : Nat.le 290000000 b) (hhi : Nat.lt b 300000000) :
    (forall n : Nat, Membership.mem ((Finset.Icc (max 4 (b * 1000000)) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun p : Nat => Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        Exists (fun q : Nat => Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\ n = p + q))) := by
  intro n hn
  by_cases h290 : b < 291000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5_sub_290 b hb hlo h290 n hn
  · by_cases h291 : b < 292000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5_sub_291 b hb (Nat.not_lt.mp h290) h291 n hn
    · by_cases h292 : b < 293000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5_sub_292 b hb (Nat.not_lt.mp h291) h292 n hn
      · by_cases h293 : b < 294000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5_sub_293 b hb (Nat.not_lt.mp h292) h293 n hn
        · by_cases h294 : b < 295000000
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5_sub_294 b hb (Nat.not_lt.mp h293) h294 n hn
          · by_cases h295 : b < 296000000
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5_sub_295 b hb (Nat.not_lt.mp h294) h295 n hn
            · by_cases h296 : b < 297000000
              · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5_sub_296 b hb (Nat.not_lt.mp h295) h296 n hn
              · by_cases h297 : b < 298000000
                · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5_sub_297 b hb (Nat.not_lt.mp h296) h297 n hn
                · by_cases h298 : b < 299000000
                  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5_sub_298 b hb (Nat.not_lt.mp h297) h298 n hn
                  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5_sub_299 b hb (Nat.not_lt.mp h298) hhi n hn
