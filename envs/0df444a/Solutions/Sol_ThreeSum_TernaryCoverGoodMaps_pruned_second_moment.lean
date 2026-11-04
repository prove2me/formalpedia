-- Prove2me | solution 1 for ThreeSum.TernaryCoverGoodMaps.pruned_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:23:31.426063+00:00
-- url     : https://prove2.me/submissions/cf3d1840-9a1d-4c33-90a7-aba7eaab2883

import Definitions.Def_Submission_ThreeSum_TernaryCoverActualMoment
import Definitions.Def_Submission_ThreeSum_Cover
import Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps
import Theorems.Thm_ThreeSum_TernaryCoverGoodMaps_prunedHit_le_raw
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverActualMoment_actual_high_moment
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
noncomputable section
open ThreeSum ThreeSum.TernaryCoverGoodMaps
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryLocalParameters TernaryCoverActualMoment TernaryCoverMoments
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]
namespace ThreeSum.TernaryCoverGoodMaps
theorem _root_.solution (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (B τ : ℕ) (a b : ZMod p) :
    (∑ w : Weight m p, prunedHit m p B τ w a b ^ 2) ≤
      3 ^ 16 * Fintype.card (Weight m p) := by
  exact (sum_le_sum (fun w _ => Nat.pow_le_pow_left (prunedHit_le_raw m p B τ w a b) 2)).trans
    (by simpa using actual_high_moment m p hp hP 2 a b)
end ThreeSum.TernaryCoverGoodMaps
