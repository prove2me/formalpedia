-- Prove2me | solution 1 for ThreeSum.TernaryCanonicalFibers.native_filter_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:59.271474+00:00
-- url     : https://prove2.me/submissions/6aaac4a4-7f8a-4475-b385-73d418c54162

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Theorems.Thm_ThreeSum_TernaryCanonicalFibers_right_native_fiber_cap
import Theorems.Thm_ThreeSum_TernaryCanonicalFibers_native_cast
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFixedDictionaries_left_native_fiber_cap
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_append
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_append
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedLittleEndian.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
namespace ThreeSum.TernaryCanonicalFibers
theorem _root_.solution (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (x : ℤ) :
    ((records (α := α) right maps B).filter
      (fun r => (p : ℤ) ∣ x-native right maps r)).length ≤ Fintype.card I*B := by
  classical
  cases right with
  | false =>
    let rs := trimmedLeftRecords (α := α) maps B
    let selected := rs.filter (fun r => (p : ℤ) ∣ x-native false maps r)
    have hn : selected.Nodup := by
      apply List.Nodup.filter
      exact Finset.nodup_toList _
    have hc : selected.toFinset.card=selected.length := List.toFinset_card_of_nodup hn
    have hsub : selected.toFinset ⊆ leftNativeFiber (α := α) maps B (x : ZMod p) := by
      intro r hr
      obtain ⟨hr,hdiv⟩ := List.mem_filter.mp (List.mem_toFinset.mp hr)
      have ha : acceptedLeft maps B r := by
        simpa only [rs,trimmedLeftRecords,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and] using hr
      have he : leftNative maps r=(x : ZMod p) := by
        have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (native false maps r) x p).mpr
          (of_decide_eq_true hdiv)
        simpa only [native_cast,Bool.false_eq_true,if_false] using h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,he⟩
    change selected.length ≤ _
    rw [← hc]
    exact (Finset.card_le_card hsub).trans (left_native_fiber_cap maps B hp _)
  | true =>
    let rs := trimmedRightRecords (α := α) maps B
    let selected := rs.filter (fun r => (p : ℤ) ∣ x-native true maps r)
    have hn : selected.Nodup := by
      apply List.Nodup.filter
      exact Finset.nodup_toList _
    have hc : selected.toFinset.card=selected.length := List.toFinset_card_of_nodup hn
    have hsub : selected.toFinset ⊆ rightNativeFiber (α := α) maps B (x : ZMod p) := by
      intro r hr
      obtain ⟨hr,hdiv⟩ := List.mem_filter.mp (List.mem_toFinset.mp hr)
      have ha : acceptedRight maps B r := by
        simpa only [rs,trimmedRightRecords,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and] using hr
      have he : rightNative maps r=(x : ZMod p) := by
        have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (native true maps r) x p).mpr
          (of_decide_eq_true hdiv)
        simpa only [native_cast,if_true] using h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,he⟩
    change selected.length ≤ _
    rw [← hc]
    exact (Finset.card_le_card hsub).trans (right_native_fiber_cap maps B hp _)
end ThreeSum.TernaryCanonicalFibers
