-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:20:41.222669+00:00
-- url     : https://prove2.me/submissions/4b2e6366-2573-4924-b675-d568e94d51c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_2_sub_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_2_sub_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_2_sub_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_2_sub_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_2_sub_5

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 360000000 <= b) (hhi : b < 370000000) :
    forall n : Nat,
      Membership.mem ((Finset.Icc (max 4 (b * 1000000))
        (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists fun p : Nat => And
        (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
        (Exists fun q : Nat => And
          (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
            (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q)
          (n = p + q)) := by
  classical
  intro n hn
  by_cases h1 : b < 362000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_2_sub_1 b hb hlo h1 n hn
  · by_cases h2 : b < 364000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_2_sub_2 b hb (by omega) h2 n hn
    · by_cases h3 : b < 366000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_2_sub_3 b hb (by omega) h3 n hn
      · by_cases h4 : b < 368000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_2_sub_4 b hb (by omega) h4 n hn
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_2_sub_5 b hb (by omega) hhi n hn
