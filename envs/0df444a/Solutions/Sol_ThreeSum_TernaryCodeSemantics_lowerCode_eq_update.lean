-- Prove2me | solution 1 for ThreeSum.TernaryCodeSemantics.lowerCode_eq_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:50.414207+00:00
-- url     : https://prove2.me/submissions/e905092e-a3b3-4eac-9724-ce0433037054

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_zeroCode_eq_update
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_oneCode_eq_update_of_pos
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
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
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryCodeSemantics
theorem _root_.solution {N : ℕ} (w : TritWord N) (i : Fin N) (d : Fin 3)
    (hd : d≤w i) : lowerCode w i d=address (Function.update w i d) := by
  fin_cases d
  · simpa [lowerCode] using zeroCode_eq_update w i
  · have hp : 0<(w i).val := by have := (show (1 : Fin 3).val≤(w i).val from hd); norm_num at this; omega
    simpa [lowerCode,Fin.ext_iff] using oneCode_eq_update_of_pos w i hp
  · have hw : w i=2 := by
      apply Fin.ext
      have ht := (w i).isLt
      have hle : (2 : Fin 3).val≤(w i).val := hd
      norm_num at hle ⊢
      omega
    have hu : Function.update w i (2 : Fin 3)=w := by
      funext j
      by_cases hj : j=i
      · subst j
        simp [hw]
      · simp [Function.update_of_ne hj]
    simp [lowerCode,Fin.ext_iff,hu]
end ThreeSum.TernaryCodeSemantics
