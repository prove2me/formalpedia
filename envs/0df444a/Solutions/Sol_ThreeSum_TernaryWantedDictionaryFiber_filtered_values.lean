-- Prove2me | solution 1 for ThreeSum.TernaryWantedDictionaryFiber.filtered_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:01.994856+00:00
-- url     : https://prove2.me/submissions/3e32b10c-3784-4d92-acc4-c1c4e5c59deb

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Theorems.Thm_ThreeSum_TernaryWantedDictionaryFiber_filter_flatMap
import Theorems.Thm_ThreeSum_TernaryWantedDictionaryFiber_filter_flatMap_ite
import Theorems.Thm_ThreeSum_TernaryWantedDictionaryFiber_flatMap_range_getD
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
import Definitions.Def_WeightedCache3SUM_Alias_7c515d7a0181c20c
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
open ThreeSum ThreeSum.TernaryWantedDictionaryFiber
open TernaryWantedRadix RadixKeyLists TernaryCanonicalFibers
namespace ThreeSum.TernaryWantedDictionaryFiber
theorem _root_.solution (p : ℤ) (hp : p ≠ 0) (raws : List ℤ) :
    ∀ j x, (values p raws j).filter (fun z => p^j ∣ x-z)=
      (wantedOutputs p raws j x).map (Radix.positionalHash p (fun i => raws.getD i 0)) := by
  intro j
  induction j with
  | zero => intro x; simp [values,wantedOutputs,Radix.positionalHash]
  | succ j ih =>
    intro x
    rw [values,step,filter_flatMap,flatMap_range_getD]
    simp only [wantedOutputs,List.map_flatMap,List.map_map,Function.comp_def,Radix.positionalHash]
    rw [localBucket,filter_flatMap_ite]
    apply List.flatMap_congr
    intro i hi
    by_cases hd : p ∣ x-raws.getD i 0
    · simp only [hd,decide_true,ite_true]
      rw [List.filter_map]
      have hpred : (fun z : ℤ => decide (p^(j+1) ∣ x-(raws.getD i 0+p*z)))=
          fun z => decide (p^j ∣ (x-raws.getD i 0)/p-z) := by
        funext z
        exact decide_eq_decide.mpr (by rw [Radix.radix_divisibility p _ _ _ hp]; simp only [hd,true_and])
      change ((values p raws j).filter (fun z => decide (p^(j+1) ∣ x-(raws.getD i 0+p*z)))).map _ = _
      rw [hpred,ih]
      simp only [List.map_map,Function.comp_def]
    · simp only [hd,decide_false,ite_false]
      apply List.filter_eq_nil_iff.mpr
      intro z hz
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
      simp only [Bool.not_eq_true,decide_eq_false_iff_not]
      intro h
      exact hd ((Radix.radix_divisibility p _ _ _ hp j).mp h).1
end ThreeSum.TernaryWantedDictionaryFiber
