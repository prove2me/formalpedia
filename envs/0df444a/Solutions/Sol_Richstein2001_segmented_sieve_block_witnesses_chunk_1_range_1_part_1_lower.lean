-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T08:52:28.85659+00:00
-- url     : https://prove2.me/submissions/8f61abc1-2fce-4cb0-b721-a572cc72f883

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp01
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp02
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp03
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp04
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp05
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp06
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp07
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp08
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp09
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp10
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp11
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp12
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp13
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp14
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp15
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp16
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp17
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp18
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp19
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp20

/-! Reduction of `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower` (blocks [50000000, 50010000)) to 20 groups of chunks: group k covers [X_k, Y_k) with X_1 = 50000000, X_{k+1} = Y_k and Y_20 = 50010000. A balanced case split on b selects the group. -/

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50000000 <= b) (hhi : b < 50010000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  rcases Nat.lt_or_ge b 50005000 with hc10 | hc10
  · rcases Nat.lt_or_ge b 50002500 with hc5 | hc5
    · rcases Nat.lt_or_ge b 50001000 with hc2 | hc2
      · rcases Nat.lt_or_ge b 50000500 with hc1 | hc1
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp01 b hb (by omega) (by omega)
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp02 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50001500 with hc3 | hc3
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp03 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50002000 with hc4 | hc4
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp04 b hb (by omega) (by omega)
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp05 b hb (by omega) (by omega)
    · rcases Nat.lt_or_ge b 50003500 with hc7 | hc7
      · rcases Nat.lt_or_ge b 50003000 with hc6 | hc6
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp06 b hb (by omega) (by omega)
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp07 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50004000 with hc8 | hc8
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp08 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50004500 with hc9 | hc9
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp09 b hb (by omega) (by omega)
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp10 b hb (by omega) (by omega)
  · rcases Nat.lt_or_ge b 50007500 with hc15 | hc15
    · rcases Nat.lt_or_ge b 50006000 with hc12 | hc12
      · rcases Nat.lt_or_ge b 50005500 with hc11 | hc11
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp11 b hb (by omega) (by omega)
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp12 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50006500 with hc13 | hc13
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp13 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50007000 with hc14 | hc14
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp14 b hb (by omega) (by omega)
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp15 b hb (by omega) (by omega)
    · rcases Nat.lt_or_ge b 50008500 with hc17 | hc17
      · rcases Nat.lt_or_ge b 50008000 with hc16 | hc16
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp16 b hb (by omega) (by omega)
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp17 b hb (by omega) (by omega)
      · rcases Nat.lt_or_ge b 50009000 with hc18 | hc18
        · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp18 b hb (by omega) (by omega)
        · rcases Nat.lt_or_ge b 50009500 with hc19 | hc19
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp19 b hb (by omega) (by omega)
          · exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp20 b hb (by omega) (by omega)
