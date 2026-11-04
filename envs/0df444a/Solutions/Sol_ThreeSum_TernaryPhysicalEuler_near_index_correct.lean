-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalEuler.near_index_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:01.863512+00:00
-- url     : https://prove2.me/submissions/681f4861-18c1-452b-94a3-6e28c88318f8

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_ordinal_spec
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_digit_canonical
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_predRank_canonical
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_near_predecessor_present
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_code_canonical
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
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
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
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



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryPhysicalEuler
theorem _root_.solution {N nn T : ℕ} (Q R : TritWord N)
    (nearWords : ℕ → TritWord N)
    (hnear : ∀ W, Below W Q → T<rank W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : ℕ) (hi : i<N)
    (hdigit : LightTernaryPredecessor.digit N (LightTernaryEulerMetadata.lowAt N i)
      (LightTernaryEulerMetadata.highAt N i) (address R)≠0)
    (hrank : T<LightTernaryPredecessor.predRank N (LightTernaryEulerMetadata.lowAt N i)
      (LightTernaryEulerMetadata.highAt N i) (address R)) :
    predecessorOrdinal nearWords nn R i<nn ∧
      address (nearWords (predecessorOrdinal nearWords nn R i))=
        LightTernaryPredecessor.code N (LightTernaryEulerMetadata.lowAt N i)
          (LightTernaryEulerMetadata.highAt N i) (address R) := by
  let fi : Fin N := ⟨i,hi⟩
  have hd : 0<(R fi).val := by rw [digit_canonical R fi] at hdigit; omega
  have hr : T<rank (predecessor R fi) := by
    rwa [predRank_canonical R fi hd] at hrank
  have ho := ordinal_spec (near_predecessor_present Q R nearWords hnear hRQ fi hr)
  have he : predecessorOrdinal nearWords nn R i=ordinal nearWords nn (predecessor R fi) := by
    simp [predecessorOrdinal,hi,fi]
  rw [he]
  refine ⟨ho.1,?_⟩
  rw [ho.2]
  exact (LightTernaryPredecessor.code_canonical R fi hd).symm
end ThreeSum.TernaryPhysicalEuler
