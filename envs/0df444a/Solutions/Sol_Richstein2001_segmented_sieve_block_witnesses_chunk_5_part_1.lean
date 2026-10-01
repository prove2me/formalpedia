-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:57:17.732717+00:00
-- url     : https://prove2.me/submissions/0cd1727b-04b4-4288-859f-8a092c2df81e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_1a
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_1b

theorem solution (b : Nat) (hb : Nat.lt b 400000001)
    (hlo : Nat.le 250000000 b) (hhi : Nat.lt b 260000000) :
    (forall n : Nat,
      Membership.mem ((Finset.Icc (max 4 (b * 1000000))
        (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun p : Nat =>
        Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        Exists (fun q : Nat =>
          Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
            (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q))) := by
  intro n hn
  by_cases hmid : Nat.lt b 255000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_1a
      b hb hlo hmid n hn
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_1b
      b hb (Nat.not_lt.mp hmid) hhi n hn
