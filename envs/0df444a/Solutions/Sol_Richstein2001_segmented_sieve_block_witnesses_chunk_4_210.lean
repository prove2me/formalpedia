-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_4_210
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:21:38.625683+00:00
-- url     : https://prove2.me/submissions/7915b917-2ced-41f0-92d6-6b2dcf40e64d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_210_part_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_210_part_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_210_part_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_210_part_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_210_part_5

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 210000000 <= b) (hhi : b < 220000000) :
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
  by_cases h212 : b < 212000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_210_part_1 b hb hlo h212 n hn
  · by_cases h214 : b < 214000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_210_part_2 b hb (by omega) h214 n hn
    · by_cases h216 : b < 216000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_210_part_3 b hb (by omega) h216 n hn
      · by_cases h218 : b < 218000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_210_part_4 b hb (by omega) h218 n hn
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_210_part_5 b hb (by omega) hhi n hn
