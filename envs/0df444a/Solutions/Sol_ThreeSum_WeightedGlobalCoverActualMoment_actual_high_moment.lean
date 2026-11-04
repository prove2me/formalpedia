-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverActualMoment.actual_high_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:34.806218+00:00
-- url     : https://prove2.me/submissions/a56fd91c-f753-473f-a859-568a67d5cabf

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverActualMoment
import Theorems.Thm_ThreeSum_WeightedGlobalCoverActualMoment_tagged_endpoint_injective
import Theorems.Thm_ThreeSum_WeightedGlobalCoverActualMoment_actual_rawEvents
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
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
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixed_mixedFiber_cap
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_bank
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverActualMoment
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryCoverHighMoment TernaryCoverRankFibers WeightedGlobalLocalParameters
open TernaryCoverOutputCap
open scoped BigOperators
namespace ThreeSum.WeightedGlobalCoverActualMoment
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
end ThreeSum.WeightedGlobalCoverActualMoment
