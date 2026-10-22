-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:42:32.716925+00:00
-- url     : https://prove2.me/submissions/43e8aed8-16a5-4991-86c2-cdb7fd24cb47

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b0
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b5
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b6
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b7
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b8
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b9

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50010070 <= b) (hhi : b < 50010080) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  by_cases h0 : b = 50010070
  · subst h0; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b0 50010070 (by omega) le_rfl (by omega)
  by_cases h1 : b = 50010071
  · subst h1; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b1 50010071 (by omega) le_rfl (by omega)
  by_cases h2 : b = 50010072
  · subst h2; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b2 50010072 (by omega) le_rfl (by omega)
  by_cases h3 : b = 50010073
  · subst h3; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b3 50010073 (by omega) le_rfl (by omega)
  by_cases h4 : b = 50010074
  · subst h4; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b4 50010074 (by omega) le_rfl (by omega)
  by_cases h5 : b = 50010075
  · subst h5; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b5 50010075 (by omega) le_rfl (by omega)
  by_cases h6 : b = 50010076
  · subst h6; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b6 50010076 (by omega) le_rfl (by omega)
  by_cases h7 : b = 50010077
  · subst h7; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b7 50010077 (by omega) le_rfl (by omega)
  by_cases h8 : b = 50010078
  · subst h8; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b8 50010078 (by omega) le_rfl (by omega)
  have h9 : b = 50010079 := by omega
  subst h9; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0008_b9 50010079 (by omega) le_rfl (by omega)
