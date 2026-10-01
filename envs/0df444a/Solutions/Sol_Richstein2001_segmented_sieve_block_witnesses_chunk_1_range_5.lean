-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:25:44.500928+00:00
-- url     : https://prove2.me/submissions/710c6fe6-a6c7-4ba8-910c-76d6501ef4d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_5_lower
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_5_upper

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 90000000 <= b) (hhi : b < 100000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  intro n hn
  by_cases hsplit : b < 95000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_5_lower
      b hb hlo hsplit n hn
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_5_upper
      b hb (by omega) hhi n hn
