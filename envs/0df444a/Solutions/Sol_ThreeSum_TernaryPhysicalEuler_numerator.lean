-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalEuler.numerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:08:33.763861+00:00
-- url     : https://prove2.me/submissions/d72b2127-2fcd-41c8-9b52-1dc8a7dbc8b9

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowWeight_eq
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_positive_read
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
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
import Theorems.Thm_ThreeSum_TernaryEuler_binomialZeta_euler
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
theorem _root_.solution {N nb nn T bv nv h : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (f : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=h) (hcut : h≤rank R)
    (hsep : bv+nb≤nv)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ i : Fin N, T<rank (predecessor R i) → ∃ j<nn, nearWords j=predecessor R i) :
    LightTernaryWeightedSum.sum (rowWeight R) (rowKey R bankWords nearWords nb nn T bv nv)
      (physicalValue (binomialZeta f) bankWords nearWords bv nv) N=
      (rank R-h : ℕ)*binomialZeta f R := by
  unfold LightTernaryWeightedSum.sum
  rw [←Fin.sum_univ_eq_sum_range]
  have he : (∑ i : Fin N, (rowWeight R i.val : ℤ)*
      physicalValue (binomialZeta f) bankWords nearWords bv nv
        (rowKey R bankWords nearWords nb nn T bv nv i.val))=
      ∑ i : Fin N, (R i).val*binomialZeta f (predecessor R i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [rowWeight_eq]
    by_cases hi : (R i).val=0
    · simp [hi]
    · have hh := positive_read R bankWords nearWords hsep hbank hnear i (by omega)
      simp only [physicalValue,hh]
  rw [he,binomialZeta_euler f h hf,Nat.cast_sub hcut]
end ThreeSum.TernaryPhysicalEuler
