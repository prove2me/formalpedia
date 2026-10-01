-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:41:59.429335+00:00
-- url     : https://prove2.me/submissions/259a4f61-e929-48c3-8163-d4f98111b315
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_2_part_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_2_part_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_2_part_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_2_part_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_2_part_5

theorem solution (b : ℕ) (hb : b < 400000001)
    (hlo : 100000000 ≤ b) (hhi : b < 150000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  intro n hn
  by_cases h₁ : b < 110000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_1 b hb hlo h₁ n hn
  · by_cases h₂ : b < 120000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_2 b hb (by omega) h₂ n hn
    · by_cases h₃ : b < 130000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_3 b hb (by omega) h₃ n hn
      · by_cases h₄ : b < 140000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_4 b hb (by omega) h₄ n hn
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_5 b hb (by omega) hhi n hn