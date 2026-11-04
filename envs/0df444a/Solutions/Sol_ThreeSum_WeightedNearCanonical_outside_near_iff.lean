-- Prove2me | solution 1 for ThreeSum.WeightedNearCanonical.outside_near_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:11:41.850549+00:00
-- url     : https://prove2.me/submissions/154e2bcb-ac69-4cd6-9324-94e6dfcc4271

import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_NearCanonical
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_WeightedCache_concrete_cost_mono
import Theorems.Thm_WeightedCache_cost_add_deficit
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedNearCanonical
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
end ThreeSum.WeightedNearCanonical
