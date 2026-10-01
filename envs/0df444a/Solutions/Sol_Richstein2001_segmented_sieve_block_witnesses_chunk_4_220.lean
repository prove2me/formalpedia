-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_4_220
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:21:40.626437+00:00
-- url     : https://prove2.me/submissions/8a7084da-194a-4726-a587-3371605c95b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_220_lower_half
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_220_upper_half

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 220000000 <= b) (hhi : b < 230000000) :
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
  by_cases hmid : b < 225000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_220_lower_half
      b hb hlo hmid n hn
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_220_upper_half
      b hb (by omega) hhi n hn
