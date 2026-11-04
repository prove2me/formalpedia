-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.global_representation_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:06.006599+00:00
-- url     : https://prove2.me/submissions/9814e882-e3a1-437d-9c5a-ce44b6b79832

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_TernaryCoverScale_repeated_scale_bound
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
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
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
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
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (c d a n r : ℕ)
    (hradix : prime (scale 40000000000 c d)^r ≤ a*n^3) (han : a ≤ n) :
    ((localFactor 40000000000 c d)^r : ℝ) ≤ (n : ℝ)^(1/10000000000 : ℝ) := by
  have hpow : (localFactor 40000000000 c d^r)^40000000000 ≤ n^4 := by
    calc
      _ ≤ prime (scale 40000000000 c d)^r := repeated_scale_bound _ _ _ _ (by decide)
      _ ≤ a*n^3 := hradix
      _ ≤ n*n^3 := Nat.mul_le_mul_right _ han
      _ = n^4 := by ring
  have hr : (((localFactor 40000000000 c d)^r : ℝ)^40000000000) ≤ (n : ℝ)^4 := by
    exact_mod_cast hpow
  have hh := (Real.le_rpow_inv_iff_of_pos
    (Nat.cast_nonneg ((localFactor 40000000000 c d)^r))
    (by positivity : (0 : ℝ) ≤ (n : ℝ)^4)
    (by norm_num : (0 : ℝ) < ((40000000000 : ℕ) : ℝ))).mpr (by
      simpa only [Real.rpow_natCast, Nat.cast_pow] using hr)
  rw [← Real.rpow_natCast (n : ℝ) 4, ← Real.rpow_mul (Nat.cast_nonneg n)] at hh
  convert hh using 1 <;> norm_num
end ThreeSum.TernaryCoverScale
