-- Prove2me | solution 1 for ThreeSum.TernaryCoverFrequency.actual_cover_frequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:48.441064+00:00
-- url     : https://prove2.me/submissions/39d0aec0-904b-44dc-bccc-9cd6943fd9bb

import Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Theorems.Thm_ThreeSum_TernaryCoverFrequency_support_frequency
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryCoverGoodMaps_pruned_first_moment
import Theorems.Thm_ThreeSum_TernaryCoverGoodMaps_pruned_second_moment
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
theorem _root_.solution (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (B k τ a : ℕ) (hτ : 0 < τ)
    (hB : 8 * (p + (fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ B * p)
    (hguard : 16*p^4*B^2*3^(4*k^2) ≤ τ^k*Fintype.card (ActualEdge m))
    (hscale : 4*p^4*3^16 ≤ a*Fintype.card (ActualEdge m)^2) (t : ZMod p × ZMod p) :
    Fintype.card (Weight m p) ≤ a * (univ.filter fun w => Covers m p B τ w t).card := by
  have hN : 0 < Fintype.card (ActualEdge m) := by
    by_contra hn
    have hz : Fintype.card (ActualEdge m) = 0 := by omega
    have hh := hscale
    rw [hz] at hh
    have hlo : 0 < 4*p^4*3^16 := by positivity
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero] at hh
    omega
  exact support_frequency (fun w => prunedHit m p B τ w t.1 t.2)
    (Fintype.card (ActualEdge m)) p (3^16) a hN
    (pruned_first_moment m p hp hP B k τ hτ hB hguard t.1 t.2)
    (pruned_second_moment m p hp hP B τ t.1 t.2) hscale
end ThreeSum.TernaryCoverFrequency
