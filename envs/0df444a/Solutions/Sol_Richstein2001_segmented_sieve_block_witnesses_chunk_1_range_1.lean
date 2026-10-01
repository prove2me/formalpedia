-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:23:48.392162+00:00
-- url     : https://prove2.me/submissions/e34396b0-d783-4d8d-9bcc-6ef069271fcd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_5
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_6
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_7
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_8
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_9
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_10

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50000000 <= b) (hhi : b < 60000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  intro n hn
  by_cases h1 : b < 51000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1 b hb hlo h1 n hn
  by_cases h2 : b < 52000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_2 b hb (by omega) h2 n hn
  by_cases h3 : b < 53000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_3 b hb (by omega) h3 n hn
  by_cases h4 : b < 54000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_4 b hb (by omega) h4 n hn
  by_cases h5 : b < 55000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_5 b hb (by omega) h5 n hn
  by_cases h6 : b < 56000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_6 b hb (by omega) h6 n hn
  by_cases h7 : b < 57000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_7 b hb (by omega) h7 n hn
  by_cases h8 : b < 58000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_8 b hb (by omega) h8 n hn
  by_cases h9 : b < 59000000
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_9 b hb (by omega) h9 n hn
  · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_10 b hb (by omega) hhi n hn
