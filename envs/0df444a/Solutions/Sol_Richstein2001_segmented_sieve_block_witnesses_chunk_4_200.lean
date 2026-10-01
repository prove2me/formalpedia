-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_4_200
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:56:55.131633+00:00
-- url     : https://prove2.me/submissions/5687d722-864a-40d5-886b-1850c8d20cf8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_200_part_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_200_part_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_200_part_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_200_part_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_200_part_5

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 200000000 <= b) (hhi : b < 210000000) :
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
  by_cases h202 : b < 202000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_200_part_1
      b hb hlo h202 n hn
  · by_cases h204 : b < 204000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_200_part_2
        b hb (by omega) h204 n hn
    · by_cases h206 : b < 206000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_200_part_3
          b hb (by omega) h206 n hn
      · by_cases h208 : b < 208000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_200_part_4
            b hb (by omega) h208 n hn
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_200_part_5
            b hb (by omega) hhi n hn