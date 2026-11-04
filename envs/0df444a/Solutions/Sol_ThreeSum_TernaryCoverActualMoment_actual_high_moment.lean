-- Prove2me | solution 1 for ThreeSum.TernaryCoverActualMoment.actual_high_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:31.991897+00:00
-- url     : https://prove2.me/submissions/fefec4bd-6165-4ef8-87ed-699cedd54990

import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverActualMoment
import Theorems.Thm_ThreeSum_TernaryCoverActualMoment_tagged_endpoint_injective
import Theorems.Thm_ThreeSum_TernaryCoverActualMoment_actual_rawEvents
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverHighMoment_raw_high_moment
import Theorems.Thm_ThreeSum_TernaryCoverOutputCap_edges_card_le
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_TernaryLocalParameters_fixed_mixedFiber_cap
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
open ThreeSum ThreeSum.TernaryCoverActualMoment
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverHighMoment TernaryCoverRankFibers TernaryLocalParameters
open TernaryCoverOutputCap
open scoped BigOperators
namespace ThreeSum.TernaryCoverActualMoment
theorem _root_.solution (m p : ℕ) [Fact p.Prime] (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (k : ℕ) (a b : ZMod p) :
    (∑ w : Coordinate (Fin (fixedLength m)) → ZMod p,
      TernaryCoverFibers.rawPairCount
        (leftHash (α := fixedAlpha m) (π := fixedPi m) w) (rightHash w) a b ^ k) ≤
      3 ^ (4*k^2) * Fintype.card (Coordinate (Fin (fixedLength m)) → ZMod p) := by
  classical
  let E := LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m)
  have hE : Fintype.card E ≤ Fintype.card (ZMod p) ^ 2 := by
    simpa [E] using (edges_card_le (L := fixedLength m) (fixedAlpha m) (fixedPi m)).trans hP
  have hprojection (β γ : ZMod p) (hn : β ≠ 0 ∨ γ ≠ 0)
      (q : Coordinate (Fin (fixedLength m)) → ZMod p) :
      (projectionFiber (fun e : E => castWord (K := ZMod p) (taggedLeft e))
        (fun e => castWord (K := ZMod p) (taggedRight e)) β γ q).card ≤ Fintype.card (ZMod p) := by
    have hsub : projectionFiber (fun e : E => castWord (K := ZMod p) (taggedLeft e))
        (fun e => castWord (K := ZMod p) (taggedRight e)) β γ q ⊆
        TernaryCoverGenericProjection.mixedFiber (fixedAlpha m) (fixedPi m) β γ (fun i => q (.inl i)) := by
      intro e he
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro i
      exact (mem_filter.mp he).2 (.inl i)
    exact (card_le_card hsub).trans (by simpa using fixed_mixedFiber_cap m p hp hP hn (fun i => q (.inl i)))
  have h := raw_high_moment (fun e : E => taggedLeft e) taggedRight
    (tagged_endpoint_injective (fixedAlpha m) (fixedPi m) (by omega : 2 < p))
    hE hprojection k a b
  rw [actual_rawEvents] at h
  simpa [E, HashFamily.incidenceCount, TernaryCoverFibers.rawPairCount,
    pairEvent, leftHash, rightHash, linearHash] using h
end ThreeSum.TernaryCoverActualMoment
