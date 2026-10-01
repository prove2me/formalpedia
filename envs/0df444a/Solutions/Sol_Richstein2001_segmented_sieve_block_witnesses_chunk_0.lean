-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_0
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:45:30.042051+00:00
-- url     : https://prove2.me/submissions/b10346ee-00d0-4c03-b259-6ab3c008e89e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_0_lower_half
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_0_upper_half

theorem solution (b : ℕ) (hb : b < 400000001) (hlo : 0 ≤ b)
    (hhi : b < 50000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  classical
  intro n hn
  by_cases hmid : b < 25000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_0_lower_half
      b hb hlo hmid n hn
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_0_upper_half
      b hb hlo (by omega) hhi n hn
