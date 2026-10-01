-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:06:30.083867+00:00
-- url     : https://prove2.me/submissions/172d6d40-50e3-4c14-9619-348b1741c1f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_1_lower_half
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_1_upper_half

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 150000000 ≤ b) (hhi : b < 160000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hnI, hnEven⟩
  rcases Finset.mem_Icc.mp hnI with ⟨hnlo, hnhi⟩
  by_cases hleft : n ≤ b * 1000000 + 499999
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_1_lower_half
      b hb hlo hhi n hn hleft
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_1_upper_half
      b hb hlo hhi n hn (by omega)
