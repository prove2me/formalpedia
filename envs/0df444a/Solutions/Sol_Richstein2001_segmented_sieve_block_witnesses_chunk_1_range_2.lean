-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:21:51.578903+00:00
-- url     : https://prove2.me/submissions/1a4f9108-b395-484b-87db-ad987c3dc081
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_2_lower
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_2_upper

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 60000000 <= b) (hhi : b < 70000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  intro n hn
  by_cases hmid : b < 65000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_2_lower
      b hb hlo hmid n hn
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_2_upper
      b hb (by omega) hhi n hn
