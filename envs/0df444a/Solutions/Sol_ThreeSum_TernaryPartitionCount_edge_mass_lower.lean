-- Prove2me | solution 1 for ThreeSum.TernaryPartitionCount.edge_mass_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:25.933223+00:00
-- url     : https://prove2.me/submissions/f568acea-45cb-4339-b56f-8b497095eefa

import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
import Theorems.Thm_ThreeSum_TernaryPartitionCount_output_group_mul_vertices_le_edges
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryCoverPartitionLower_partitionCap_le_poly_mul_group
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
    (vertices (t+2*r+3*s) (piType t r s)).card*(2^(2*r)*3^(3*s)) ≤
    partitionLoss r s*Fintype.card
      (LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s)) := by
  have hp : 2^(2*r)*3^(3*s) ≤ partitionLoss r s*partitionGroup r s := by
    simpa [partitionLoss,partitionGroup,Nat.mul_assoc] using
      TernaryCoverPartitionLower.partitionCap_le_poly_mul_group r s
  have he := output_group_mul_vertices_le_edges t r s
  calc
    _ ≤ (vertices (t+2*r+3*s) (piType t r s)).card*(partitionLoss r s*partitionGroup r s) :=
      Nat.mul_le_mul_left _ hp
    _ = partitionLoss r s*((vertices (t+2*r+3*s) (piType t r s)).card*partitionGroup r s) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ he
end ThreeSum.TernaryPartitionCount
