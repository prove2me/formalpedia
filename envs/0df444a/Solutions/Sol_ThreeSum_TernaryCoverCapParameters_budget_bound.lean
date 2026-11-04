-- Prove2me | solution 1 for ThreeSum.TernaryCoverCapParameters.budget_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:11.548947+00:00
-- url     : https://prove2.me/submissions/1f6ca5f0-a4da-4198-9cc1-8c35b5445085

import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
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
open ThreeSum ThreeSum.TernaryCoverCapParameters
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps TernaryCoverFrequency TernaryPartitionCount TernaryTypeLowerBound
namespace ThreeSum.TernaryCoverCapParameters
theorem _root_.solution (p B k : ℕ) : 16*p^4*B^2*3^(4*k^2) ≤ 2^capBudget p B k := by
  have hp : p^4 ≤ 2^(4*(Nat.log2 p+1)) := by
    have h := Nat.pow_le_pow_left (Nat.lt_log2_self (n := p)).le 4
    simpa only [← pow_mul, Nat.mul_comm] using h
  have hB : B^2 ≤ 2^(2*(Nat.log2 B+1)) := by
    have h := Nat.pow_le_pow_left (Nat.lt_log2_self (n := B)).le 2
    simpa only [← pow_mul, Nat.mul_comm] using h
  have h3 : 3^(4*k^2) ≤ 2^(8*k^2) := by
    have h := Nat.pow_le_pow_left (by decide : (3 : ℕ) ≤ 2^2) (4*k^2)
    simpa only [← pow_mul, show 2*(4*k^2) = 8*k^2 by ring] using h
  calc
    _ ≤ 16*2^(4*(Nat.log2 p+1))*2^(2*(Nat.log2 B+1))*2^(8*k^2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 16 hp) hB) h3
    _ = 2^capBudget p B k := by
      rw [show (16 : ℕ) = 2^4 by norm_num, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      unfold capBudget
      omega
end ThreeSum.TernaryCoverCapParameters
