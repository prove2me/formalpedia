-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T11:46:38.292072+00:00
-- url     : https://prove2.me/submissions/fbc993be-b392-412f-b55d-44f6e1bdc4d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper

/-! Reduction of `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1` to `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower` (blocks [50000000, 50010000)) and `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper` (blocks [50010000, 51000000)). -/

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50000000 <= b) (hhi : b < 51000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  rcases Nat.lt_or_ge b 50010000 with h | h
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower b hb hlo h
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper b hb h hhi
