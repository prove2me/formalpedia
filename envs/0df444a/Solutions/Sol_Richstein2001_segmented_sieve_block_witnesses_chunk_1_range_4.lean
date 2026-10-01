-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:21:54.227912+00:00
-- url     : https://prove2.me/submissions/3c4e2346-3f7c-4ea2-9949-c3bed54e1035
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4_part_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4_part_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4_part_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4_part_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4_part_5
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4_part_6
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4_part_7
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4_part_8
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4_part_9
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4_part_10

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 80000000 <= b) (hhi : b < 90000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  intro n hn
  by_cases h1 : b < 81000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4_part_1 b hb hlo h1 n hn
  · by_cases h2 : b < 82000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4_part_2 b hb (by omega) h2 n hn
    · by_cases h3 : b < 83000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4_part_3 b hb (by omega) h3 n hn
      · by_cases h4 : b < 84000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4_part_4 b hb (by omega) h4 n hn
        · by_cases h5 : b < 85000000
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4_part_5 b hb (by omega) h5 n hn
          · by_cases h6 : b < 86000000
            · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4_part_6 b hb (by omega) h6 n hn
            · by_cases h7 : b < 87000000
              · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4_part_7 b hb (by omega) h7 n hn
              · by_cases h8 : b < 88000000
                · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4_part_8 b hb (by omega) h8 n hn
                · by_cases h9 : b < 89000000
                  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4_part_9 b hb (by omega) h9 n hn
                  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4_part_10 b hb (by omega) hhi n hn
