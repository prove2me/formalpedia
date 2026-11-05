-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical.outside_near_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:45:01.45749+00:00
-- url     : https://prove2.me/submissions/d32b484b-7a66-4e1b-ace5-6911ad7e1fdd

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearPair
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearCanonical
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_concrete_cost_mono
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_cost_add_deficit
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.mem_nearWords



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical
theorem _root_.solution {N : ℕ} (Q R : TritWord N) (T : ℕ) (hQ : T<cacheCost Q) :
    R∈nearWords Q (cacheCost Q-(T+1)) ↔ Below R Q ∧ T<cacheCost R := by
  rw [mem_nearWords]
  constructor
  · intro ⟨hbelow,hdef⟩
    have hsum := WeightedCache.cost_add_deficit WeightedCache.concrete_cost_mono hbelow
    change cacheCost R + WeightedNearBankEnumeration.deficit Q R = cacheCost Q at hsum
    exact ⟨hbelow,by omega⟩
  · intro ⟨hbelow,hrank⟩
    have hsum := WeightedCache.cost_add_deficit WeightedCache.concrete_cost_mono hbelow
    change cacheCost R + WeightedNearBankEnumeration.deficit Q R = cacheCost Q at hsum
    exact ⟨hbelow,by omega⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearCanonical
