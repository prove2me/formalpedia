-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:09:37.086748+00:00
-- url     : https://prove2.me/submissions/802d6e88-2485-46af-9cc9-f96410d840e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_5

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50000000 <= b) (hhi : b < 100000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  intro n hn
  by_cases h1 : b < 60000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1 b hb (by omega) h1 n hn
  · by_cases h2 : b < 70000000
    · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_2 b hb (by omega) h2 n hn
    · by_cases h3 : b < 80000000
      · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_3 b hb (by omega) h3 n hn
      · by_cases h4 : b < 90000000
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4 b hb (by omega) h4 n hn
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_5 b hb (by omega) hhi n hn