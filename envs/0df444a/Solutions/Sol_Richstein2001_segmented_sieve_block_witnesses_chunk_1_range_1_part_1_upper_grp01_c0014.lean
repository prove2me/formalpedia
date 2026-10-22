-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:05:41.152966+00:00
-- url     : https://prove2.me/submissions/2768c6f9-e8de-40b4-baf1-e743c0dd4cc2

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b0
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b5
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b6
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b7
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b8
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b9

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50010130 <= b) (hhi : b < 50010140) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  by_cases h0 : b = 50010130
  · subst h0; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b0 50010130 (by omega) le_rfl (by omega)
  by_cases h1 : b = 50010131
  · subst h1; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b1 50010131 (by omega) le_rfl (by omega)
  by_cases h2 : b = 50010132
  · subst h2; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b2 50010132 (by omega) le_rfl (by omega)
  by_cases h3 : b = 50010133
  · subst h3; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b3 50010133 (by omega) le_rfl (by omega)
  by_cases h4 : b = 50010134
  · subst h4; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b4 50010134 (by omega) le_rfl (by omega)
  by_cases h5 : b = 50010135
  · subst h5; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b5 50010135 (by omega) le_rfl (by omega)
  by_cases h6 : b = 50010136
  · subst h6; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b6 50010136 (by omega) le_rfl (by omega)
  by_cases h7 : b = 50010137
  · subst h7; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b7 50010137 (by omega) le_rfl (by omega)
  by_cases h8 : b = 50010138
  · subst h8; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b8 50010138 (by omega) le_rfl (by omega)
  have h9 : b = 50010139 := by omega
  subst h9; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0014_b9 50010139 (by omega) le_rfl (by omega)
