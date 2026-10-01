-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:39:03.178039+00:00
-- url     : https://prove2.me/submissions/5a1ed80b-6702-4e9f-97ea-2660b63bd61e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_5

theorem solution (b : ℕ) (hb : b < 400000001)
    (hlo : 350000000 ≤ b) (hhi : b < 400000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  classical
  intro n hn
  by_cases h1 : b < 360000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_1 b hb hlo h1 n hn
  · by_cases h2 : b < 370000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_2 b hb (by omega) h2 n hn
    · by_cases h3 : b < 380000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_3 b hb (by omega) h3 n hn
      · by_cases h4 : b < 390000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_4 b hb (by omega) h4 n hn
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_5 b hb (by omega) hhi n hn
