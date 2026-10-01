-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:06:54.522243+00:00
-- url     : https://prove2.me/submissions/02d75c9d-9bd9-44f8-88e3-53d315eb12be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_2_part_1_lower
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_2_part_1_upper

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 100000000 ≤ b) (hhi : b < 110000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  intro n hn
  by_cases hmid : b < 105000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_1_lower b hb hlo hmid n hn
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_1_upper b hb (Nat.le_of_not_lt hmid) hhi n hn