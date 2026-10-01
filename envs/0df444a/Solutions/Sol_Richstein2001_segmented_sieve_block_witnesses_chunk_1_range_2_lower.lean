-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_2_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-27T23:03:51.169434+00:00
-- url     : https://prove2.me/submissions/2089d70f-12e6-4853-8d08-37143261e2e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_2

set_option autoImplicit false

-- Top-level `solution` (NOT inside `namespace Richstein2001`): the platform checks
-- this declaration against the target's formal_statement.
theorem solution (b : Nat) (hb : b < 400000001) (hlo : 60000000 <= b)
    (hhi : b < 65000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  intro n hn
  exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_2 b hb hlo
    (by omega) n hn
