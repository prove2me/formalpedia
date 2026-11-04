-- Prove2me | solution 1 for ThreeSum.TernaryCoverFrequency.covers_raw_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:57.814562+00:00
-- url     : https://prove2.me/submissions/89fe6ab8-cd61-4e3b-a8da-892c70823c1c

import Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryCoverLocal_rawCap_le_iff
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
open ThreeSum ThreeSum.TernaryCoverFrequency
open Finset TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]
namespace ThreeSum.TernaryCoverFrequency
theorem _root_.solution {B τ : ℕ} {w : Weight m p} {t : ZMod p × ZMod p}
    (hc : Covers m p B τ w t) : rawCap (fixedAlpha m) (fixedPi m) w ≤ τ := by
  classical
  apply (rawCap_le_iff (fixedAlpha m) (fixedPi m) w τ).mpr
  intro a b
  by_contra hn
  have hb : w ∈ rawBadMaps m p τ := mem_filter.mpr
    ⟨mem_univ _, ⟨(a,b), Nat.lt_of_not_ge hn⟩⟩
  simp [Covers, prunedHit, hb] at hc
end ThreeSum.TernaryCoverFrequency
