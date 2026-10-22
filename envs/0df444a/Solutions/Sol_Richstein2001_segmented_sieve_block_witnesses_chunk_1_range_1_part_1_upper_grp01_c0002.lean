-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:16:29.141039+00:00
-- url     : https://prove2.me/submissions/aea5cf39-ecd5-4477-b657-7432b20af821

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b0
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b5
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b6
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b7
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b8
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b9

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50010010 <= b) (hhi : b < 50010020) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  by_cases h0 : b = 50010010
  · subst h0; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b0 50010010 (by omega) le_rfl (by omega)
  by_cases h1 : b = 50010011
  · subst h1; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b1 50010011 (by omega) le_rfl (by omega)
  by_cases h2 : b = 50010012
  · subst h2; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b2 50010012 (by omega) le_rfl (by omega)
  by_cases h3 : b = 50010013
  · subst h3; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b3 50010013 (by omega) le_rfl (by omega)
  by_cases h4 : b = 50010014
  · subst h4; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b4 50010014 (by omega) le_rfl (by omega)
  by_cases h5 : b = 50010015
  · subst h5; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b5 50010015 (by omega) le_rfl (by omega)
  by_cases h6 : b = 50010016
  · subst h6; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b6 50010016 (by omega) le_rfl (by omega)
  by_cases h7 : b = 50010017
  · subst h7; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b7 50010017 (by omega) le_rfl (by omega)
  by_cases h8 : b = 50010018
  · subst h8; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b8 50010018 (by omega) le_rfl (by omega)
  have h9 : b = 50010019 := by omega
  subst h9; exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b9 50010019 (by omega) le_rfl (by omega)
