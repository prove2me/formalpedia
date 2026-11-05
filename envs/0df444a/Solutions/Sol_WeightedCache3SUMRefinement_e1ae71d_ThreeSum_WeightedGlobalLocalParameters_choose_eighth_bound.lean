-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters.choose_eighth_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:07:26.360125+00:00
-- url     : https://prove2.me/submissions/0556fda7-6717-480e-9e73-2cc5d0bfa695

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
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
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters
theorem _root_.solution (m k : ℕ) (hk : k ≤ 8*m) :
    (8*m).choose k ≤ 2^(m+4*k) := by
  have h := single_le_sum
    (s := range (8*m+1)) (f := fun i => (1 : ℕ)^i*16^(8*m-i)*(8*m).choose i)
    (fun i _ => Nat.zero_le _) (mem_range.mpr (by omega : k < 8*m+1))
  have hadd : (17 : ℕ)^(8*m) =
      ∑ i ∈ range (8*m+1), (1 : ℕ)^i*16^(8*m-i)*(8*m).choose i := by
    simpa only [Nat.cast_id,Nat.reduceAdd] using add_pow (1 : ℕ) 16 (8*m)
  rw [← hadd] at h
  simp only [one_pow,one_mul,Nat.reduceAdd] at h
  have hp : 17^(8*m) ≤ 2^m*16^(8*m) := by
    have hh := Nat.pow_le_pow_left (by norm_num : (17 : ℕ)^8 ≤ 2*16^8) m
    simpa only [mul_pow,← pow_mul] using hh
  have hm := Nat.mul_le_mul_right (16^k) (h.trans hp)
  have he : 16^(8*m-k)*16^k = 16^(8*m) := by
    rw [← pow_add,Nat.sub_add_cancel hk]
  have hc : (8*m).choose k*16^(8*m) ≤ (2^m*16^k)*16^(8*m) := by
    calc
      _ = (16^(8*m-k)*(8*m).choose k)*16^k := by rw [← he]; ring
      _ ≤ (2^m*16^(8*m))*16^k := hm
      _ = _ := by ring
  have hh := Nat.le_of_mul_le_mul_right hc (by positivity : 0 < 16^(8*m))
  calc
    _ ≤ 2^m*16^k := hh
    _ = 2^(m+4*k) := by rw [show (16 : ℕ) = 2^4 by norm_num,← pow_mul,← pow_add]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalLocalParameters
