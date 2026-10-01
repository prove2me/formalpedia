-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:42:39.664463+00:00
-- url     : https://prove2.me/submissions/e8a10370-6ead-490c-973c-c512755a060d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_200
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_210
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_220
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_230
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_240

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 200000000 <= b) (hhi : b < 250000000) :
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
  by_cases h210 : b < 210000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_200
      b hb hlo h210 n hn
  · by_cases h220 : b < 220000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_210
        b hb (by omega) h220 n hn
    · by_cases h230 : b < 230000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_220
          b hb (by omega) h230 n hn
      · by_cases h240 : b < 240000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_230
            b hb (by omega) h240 n hn
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_4_240
            b hb (by omega) hhi n hn
