-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_4_240
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:55:04.994973+00:00
-- url     : https://prove2.me/submissions/e461e424-da32-42cb-8677-fd4d94adf44b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_240_lower_half
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_240_upper_half

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 240000000 <= b) (hhi : b < 250000000) :
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
  by_cases hmid : b < 245000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_240_lower_half
      b hb hlo hmid n hn
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_240_upper_half
      b hb (by omega) hhi n hn
