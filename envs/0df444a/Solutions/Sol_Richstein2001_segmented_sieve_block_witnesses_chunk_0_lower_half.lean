-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_0_lower_half
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-27T21:30:20.90816+00:00
-- url     : https://prove2.me/submissions/a3c16b99-ca5e-4455-bb5e-2ca0ecedcb0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses

set_option autoImplicit false

-- Top-level `solution`: the platform checks this declaration against the target's
-- formal_statement, so it must NOT be wrapped in `namespace Richstein2001`.
theorem solution (b : Nat)
    (hb : b < 400000001) (hlo : LE.le 0 b) (hhi : b < 25000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun (p : Nat) => And (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
        (Exists (fun (q : Nat) => And (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q)
          (n = p + q)))) := by
  intro n hn
  exact Richstein2001.segmented_sieve_block_witnesses b hb n hn
