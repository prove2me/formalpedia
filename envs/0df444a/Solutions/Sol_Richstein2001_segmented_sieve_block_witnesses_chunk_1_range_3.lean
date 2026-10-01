-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:20:56.664289+00:00
-- url     : https://prove2.me/submissions/a76868b4-d9bd-40f1-bbc1-3e0d7283e476
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_3_lower
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_3_upper

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 70000000 <= b) (hhi : b < 80000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  intro n hn
  by_cases hmid : b < 75000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_3_lower
      b hb hlo hmid n hn
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_3_upper
      b hb (by omega) hhi n hn
