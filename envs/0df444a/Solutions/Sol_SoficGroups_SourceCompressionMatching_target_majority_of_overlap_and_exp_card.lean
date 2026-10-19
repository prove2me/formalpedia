-- Prove2me | solution 1 for SoficGroups.SourceCompressionMatching.target_majority_of_overlap_and_exp_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/323ca8d5-66f3-451f-8b09-bd778cb37b1c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_target_majority_of_small_symmDiff
import Theorems.Thm_SoficGroups_SourceCompressionMatching_symmDiff_card_lt_of_overlap_and_exp_card

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionMatching
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.SourceCompressionMatching
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    (C D : Finset V) (hC : C.Nonempty) (H eta : ℝ)
    (hoverlap :
      (1 - eta) * (C.card : ℝ) ≤ ((C ∩ D).card : ℝ))
    (hcard : (D.card : ℝ) < Real.exp H * (C.card : ℝ))
    (hsmall : 2 * (Real.exp H - 1 + 2 * eta) < 1) :
    D.card < 2 * (C ∩ D).card := by
  have hbound :=
    symmDiff_card_lt_of_overlap_and_exp_card C D H eta hoverlap hcard
  have hpositive : (0 : ℝ) < C.card := by
    exact_mod_cast hC.card_pos
  have hreal :
      (2 : ℝ) * ((C ∆ D).card : ℝ) < (C.card : ℝ) := by
    calc
      (2 : ℝ) * ((C ∆ D).card : ℝ) <
          2 * ((Real.exp H - 1 + 2 * eta) * (C.card : ℝ)) :=
        mul_lt_mul_of_pos_left hbound (by norm_num)
      _ = (2 * (Real.exp H - 1 + 2 * eta)) * (C.card : ℝ) := by
        ring
      _ < 1 * (C.card : ℝ) :=
        mul_lt_mul_of_pos_right hsmall hpositive
      _ = (C.card : ℝ) := one_mul _
  have hnat : 2 * (C ∆ D).card < C.card := by
    exact_mod_cast hreal
  exact SoficGroups.target_majority_of_small_symmDiff C D hnat
end SoficGroups.SourceCompressionMatching
