-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:42:54.748497+00:00
-- url     : https://prove2.me/submissions/47098689-be48-4edc-a6d9-2b2ca56580e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_5

theorem solution (b : Nat) (hb : b < 400000001) (hlo : 300000000 ≤ b)
    (hhi : b < 350000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  intro n hn
  by_cases h1 : b < 310000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_1 b hb hlo h1 n hn
  · by_cases h2 : b < 320000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_2 b hb (by omega) h2 n hn
    · by_cases h3 : b < 330000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_3 b hb (by omega) h3 n hn
      · by_cases h4 : b < 340000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_4 b hb (by omega) h4 n hn
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5 b hb (by omega) hhi n hn
