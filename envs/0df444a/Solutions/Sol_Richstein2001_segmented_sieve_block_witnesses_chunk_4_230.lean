-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_4_230
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:55:50.119947+00:00
-- url     : https://prove2.me/submissions/994c05b3-43b5-4662-9a69-ab7d2125ad0e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_230_lower_half
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_230_upper_half

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 230000000 <= b) (hhi : b < 240000000) :
    forall n : Nat,
      Membership.mem ((Finset.Icc (max 4 (b * 1000000))
        (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      (Exists fun p : Nat => And
        (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
        (Exists fun q : Nat => And
          (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
            (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q)
          (n = p + q))) := by
  classical
  intro n hn
  by_cases hmid : b < 235000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_230_lower_half
      b hb hlo hmid n hn
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_230_upper_half
      b hb (by omega) hhi n hn
