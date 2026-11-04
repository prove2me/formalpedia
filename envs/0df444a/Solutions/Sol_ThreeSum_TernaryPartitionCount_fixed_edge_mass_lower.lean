-- Prove2me | solution 1 for ThreeSum.TernaryPartitionCount.fixed_edge_mass_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:46.39739+00:00
-- url     : https://prove2.me/submissions/c30f8d26-1fcb-4b8c-8047-5ee9611efb80

import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
import Theorems.Thm_ThreeSum_TernaryPartitionCount_edge_mass_lower
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
open TernaryLocalParameters
namespace ThreeSum.TernaryPartitionCount
theorem _root_.solution (m : ℕ) :
    (vertices (fixedLength m) (fixedPi m)).card*(2^(fixedPi m 1)*3^(fixedPi m 2)) ≤
    partitionLoss (7930225*m) (978268*m)*
      Fintype.card (LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m)) := by
  have h := edge_mass_lower (81204746*m) (7930225*m) (978268*m)
  have hL : 81204746*m+2*(7930225*m)+3*(978268*m) = fixedLength m := by
    simp [fixedLength]; omega
  have hα : alphaType (81204746*m) (7930225*m) (978268*m) = fixedAlpha m := by
    funext d
    fin_cases d <;> simp [alphaType,fixedAlpha] <;> omega
  have hπ : piType (81204746*m) (7930225*m) (978268*m) = fixedPi m := by
    funext d
    fin_cases d <;> simp [piType,fixedPi] <;> omega
  have h1 : 2*(7930225*m) = fixedPi m 1 := by simp [fixedPi]; omega
  have h2 : 3*(978268*m) = fixedPi m 2 := by simp [fixedPi]; omega
  rw [hL,hα,hπ,h1,h2] at h
  exact h
end ThreeSum.TernaryPartitionCount
