-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T14:09:48.551267+00:00
-- url     : https://prove2.me/submissions/fad63c6e-f801-4d6e-b2cf-eadb236df534
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_5_sub_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_5_sub_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_5_sub_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_5_sub_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_5_sub_5

theorem solution (b : ℕ) (hb : b < 400000001)
    (hlo : 390000000 ≤ b) (hhi : b < 400000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  classical
  intro n hn
  by_cases h1 : b < 392000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_5_sub_1 b hb hlo h1 n hn
  · by_cases h2 : b < 394000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_5_sub_2 b hb (by omega) h2 n hn
    · by_cases h3 : b < 396000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_5_sub_3 b hb (by omega) h3 n hn
      · by_cases h4 : b < 398000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_5_sub_4 b hb (by omega) h4 n hn
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_5_sub_5 b hb (by omega) hhi n hn
