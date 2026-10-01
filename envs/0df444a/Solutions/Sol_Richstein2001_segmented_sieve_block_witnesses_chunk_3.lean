-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:23:50.6082+00:00
-- url     : https://prove2.me/submissions/d3811f7a-780b-4b45-9f8b-d10fe4027028
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_5

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 150000000 ≤ b) (hhi : b < 200000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  intro n hn
  by_cases h₁ : b < 160000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_1 b hb (by omega) (by omega) n hn
  · by_cases h₂ : b < 170000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_2 b hb (by omega) (by omega) n hn
    · by_cases h₃ : b < 180000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_3 b hb (by omega) (by omega) n hn
      · by_cases h₄ : b < 190000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_4 b hb (by omega) (by omega) n hn
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_5 b hb (by omega) (by omega) n hn