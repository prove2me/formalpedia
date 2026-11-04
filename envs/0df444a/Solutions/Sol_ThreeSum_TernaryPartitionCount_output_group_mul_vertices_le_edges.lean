-- Prove2me | solution 1 for ThreeSum.TernaryPartitionCount.output_group_mul_vertices_le_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:41.37259+00:00
-- url     : https://prove2.me/submissions/937972ba-71da-43ac-8cf0-462febb2c377

import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
import Theorems.Thm_ThreeSum_TernaryPartitionCount_output_partitionGroup_lower
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data
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
theorem _root_.solution (t r s : ℕ) :
    (vertices (t+2*r+3*s) (piType t r s)).card*partitionGroup r s ≤
    Fintype.card (LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s)) := by
  classical
  let L := t+2*r+3*s
  let α := alphaType t r s
  let π := piType t r s
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset (LocalEdge L α π)))
    (t := vertices L π) (f := output)
    (fun e _ => mem_filter.mpr ⟨mem_univ _,(edge_data e).2.2.1⟩)
  calc
    _ = ∑ _q ∈ vertices L π, partitionGroup r s := by simp [L,π]
    _ ≤ ∑ q ∈ vertices L π, (univ.filter (fun e : LocalEdge L α π => output e = q)).card := by
      apply sum_le_sum
      intro q hq
      rw [← Fintype.card_subtype]
      exact output_partitionGroup_lower t r s q ((mem_filter.mp hq).2)
    _ = _ := by simpa only [card_univ] using h.symm
end ThreeSum.TernaryPartitionCount
