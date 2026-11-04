-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.polynomial_schedule_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:26:34.711511+00:00
-- url     : https://prove2.me/submissions/bd6d7c3f-757c-4b6a-95ea-13f52830b394

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_TernaryCoverScale_schedule_upper
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
theorem _root_.solution (c d t : ℕ) (hc : c ≤ t) :
    (c*(fixedLength (2^(2*t))+1)^d)*
      (frequencyFactor (2^(2*t))*(Nat.log2 (prime (2^(2*t))^2)+1)) ≤
    2^(28*d+241+(2*d+15)*t) := by
  have hc2 : c ≤ 2^t := hc.trans (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))))
  have hm : 2^(2*t)+1 ≤ 2^(2*t+1) := by rw [pow_succ]; have := Nat.one_le_pow (2*t) 2 (by decide); omega
  have hL : fixedLength (2^(2*t))+1 ≤ 2^27*(2^(2*t)+1) := by simp [fixedLength]; norm_num; omega
  have hb := Nat.mul_le_mul (Nat.mul_le_mul hc2 (Nat.pow_le_pow_left hL d)) (schedule_upper (2^(2*t)))
  calc
    _ ≤ (2^t*(2^27*(2^(2*t)+1))^d)*(2^234*(2^(2*t)+1)^7) := hb
    _ = 2^(t+27*d+234)*(2^(2*t)+1)^(d+7) := by rw [mul_pow, ← pow_mul, pow_add]; ring
    _ ≤ 2^(t+27*d+234)*(2^(2*t+1))^(d+7) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm _)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring
end ThreeSum.TernaryCoverScale
