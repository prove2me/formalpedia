-- Prove2me | solution 1 for ThreeSum.TernaryPartitionCount.partLeft_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:09.081667+00:00
-- url     : https://prove2.me/submissions/1e22a1ad-b1ba-4f50-a08d-3302d880e8c4

import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
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
open ThreeSum ThreeSum.TernaryPartitionCount
open Finset TernaryJointType TernaryCoverLocal TernaryCoverRegularity TernaryCoverOutputCap
open TernaryTypeLowerBound
namespace ThreeSum.TernaryPartitionCount
theorem _root_.solution {t r s : ℕ} : Function.Injective (partLeft (t := t) (r := r) (s := s)) := by
  intro c d h
  apply Prod.ext
  · apply Subtype.ext
    ext i
    have hi := congrFun h (Sum.inr (Sum.inl i))
    by_cases hc : i ∈ c.1.val <;> by_cases hd : i ∈ d.1.val <;> simp_all [partLeft]
  · apply Subtype.ext
    apply Prod.ext
    · ext i
      have hi := congrFun h (Sum.inr (Sum.inr i))
      have hc := disjoint_left.mp (LayerCounts.mem_edgeSet.mp c.2.property).2.2
      have hd := disjoint_left.mp (LayerCounts.mem_edgeSet.mp d.2.property).2.2
      by_cases hcT : i ∈ c.2.val.1 <;> by_cases hcU : i ∈ c.2.val.2 <;>
        by_cases hdT : i ∈ d.2.val.1 <;> by_cases hdU : i ∈ d.2.val.2 <;> simp_all [partLeft]
    · ext i
      have hi := congrFun h (Sum.inr (Sum.inr i))
      have hc := disjoint_left.mp (LayerCounts.mem_edgeSet.mp c.2.property).2.2
      have hd := disjoint_left.mp (LayerCounts.mem_edgeSet.mp d.2.property).2.2
      by_cases hcT : i ∈ c.2.val.1 <;> by_cases hcU : i ∈ c.2.val.2 <;>
        by_cases hdT : i ∈ d.2.val.1 <;> by_cases hdU : i ∈ d.2.val.2 <;> simp_all [partLeft]
end ThreeSum.TernaryPartitionCount
