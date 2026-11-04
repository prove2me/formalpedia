-- Prove2me | solution 1 for ThreeSum.TernaryCoverGoodMaps.pruned_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:22.948227+00:00
-- url     : https://prove2.me/submissions/47e485e2-4301-4982-823c-5ab740434599

import Definitions.Def_Submission_ThreeSum_TernaryCoverActualMoment
import Definitions.Def_Submission_ThreeSum_Cover
import Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps
import Theorems.Thm_ThreeSum_TernaryCoverGoodMaps_rawBadMaps_count_bound
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverLocal_first_moment
import Theorems.Thm_ThreeSum_TernaryCoverLocal_hitCount_cap
import Theorems.Thm_ThreeSum_TernaryCoverMoments_removed_mass_bound
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
    (B k τ : ℕ) (hτ : 0 < τ)
    (hB : 8 * (p + (fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ B * p)
    (hguard : 16*p^4*B^2*3^(4*k^2) ≤ τ^k*Fintype.card (ActualEdge m))
    (a b : ZMod p) :
    Fintype.card (ActualEdge m) * Fintype.card (Weight m p) ≤
      2 * p ^ 2 * ∑ w, prunedHit m p B τ w a b := by
  classical
  have hbad := rawBadMaps_count_bound m p hp hP k τ
  have hloss : 16*p^2*B^2*(rawBadMaps m p τ).card ≤
      Fintype.card (ActualEdge m)*Fintype.card (Weight m p) := by
    apply Nat.le_of_mul_le_mul_left (c := τ^k) ?_ (Nat.pow_pos hτ)
    calc
      _ = 16*p^2*B^2*(τ^k*(rawBadMaps m p τ).card) := by ring
      _ ≤ 16*p^2*B^2*(p^2*3^(4*k^2)*Fintype.card (Weight m p)) :=
        Nat.mul_le_mul_left _ hbad
      _ = (16*p^4*B^2*3^(4*k^2))*Fintype.card (Weight m p) := by ring
      _ ≤ (τ^k*Fintype.card (ActualEdge m))*Fintype.card (Weight m p) :=
        Nat.mul_le_mul_right _ hguard
      _ = _ := by ring
  have hremoved := removed_mass_bound
    (fun w : Weight m p => hitCount (fixedAlpha m) (fixedPi m) B w a b)
    (rawBadMaps m p τ) B (fun w => hitCount_cap _ _ B w a b (by omega : 2 < p))
  have hsum : (∑ w : Weight m p, hitCount (fixedAlpha m) (fixedPi m) B w a b) =
      (∑ w, prunedHit m p B τ w a b) +
        ∑ w ∈ rawBadMaps m p τ, hitCount (fixedAlpha m) (fixedPi m) B w a b := by
    have heq : (univ : Finset (Weight m p)).filter (fun w => w ∈ rawBadMaps m p τ) =
        rawBadMaps m p τ := by ext w; simp
    rw [← heq, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro w _
    by_cases hw : w ∈ rawBadMaps m p τ <;> simp [prunedHit, hw]
  have hfirst := first_moment (L := fixedLength m) (p := p)
    (fixedAlpha m) (fixedPi m) B a b hB
  rw [hsum] at hfirst
  have hm := Nat.mul_le_mul_left (16*p^2) hremoved
  nlinarith
end ThreeSum.TernaryCoverGoodMaps
