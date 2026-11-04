-- Prove2me | solution 1 for ThreeSum.WeightedGlobalLocalParameters.difference_choose_le_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:10:16.286826+00:00
-- url     : https://prove2.me/submissions/f32ba50d-ceef-4042-abd4-df00ac560fc5

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_choose_eighth_bound
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection
namespace ThreeSum.WeightedGlobalLocalParameters
theorem _root_.solution (m : ℕ) :
    (fixedLength m).choose (fixedPi m 2/3) ≤ 2^(fixedPi m 1)*3^(fixedPi m 2) := by
  have hk : 292746547000*m ≤ 8*(3750000000000*m) := by omega
  have h := choose_eighth_bound (3750000000000*m) (292746547000*m) hk
  have hL : 8*(3750000000000*m) = fixedLength m := by simp [fixedLength]; omega
  have hr : 292746547000*m = fixedPi m 2/3 := by simp [fixedPi]; omega
  rw [hL,hr] at h
  calc
    _ ≤ 2^(3750000000000*m+4*(fixedPi m 2/3)) := h
    _ ≤ 2^(fixedPi m 1+fixedPi m 2) :=
      Nat.pow_le_pow_right (by decide) (by simp [fixedPi]; omega)
    _ = 2^(fixedPi m 1)*2^(fixedPi m 2) := pow_add _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)
end ThreeSum.WeightedGlobalLocalParameters
