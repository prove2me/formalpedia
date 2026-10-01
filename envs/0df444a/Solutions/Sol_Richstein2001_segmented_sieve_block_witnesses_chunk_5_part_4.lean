-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:54:25.884201+00:00
-- url     : https://prove2.me/submissions/bf248182-917d-44f1-bf06-324481f7da6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_4_first_half
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_4_second_half

theorem solution (b : Nat) (hb : Nat.lt b 400000001)
    (hlo : Nat.le 280000000 b) (hhi : Nat.lt b 290000000) :
    (forall n : Nat, Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun p : Nat => Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        Exists (fun q : Nat => Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\ n = p + q))) := by
  by_cases hmid : Nat.lt b 285000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_4_first_half
      b hb hlo hmid
  · have hmid' : Nat.le 285000000 b := Nat.not_lt.mp hmid
    exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_4_second_half
      b hb hmid' hhi
