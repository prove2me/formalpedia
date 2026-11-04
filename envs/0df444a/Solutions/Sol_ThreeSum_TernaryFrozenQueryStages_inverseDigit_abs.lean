-- Prove2me | solution 1 for ThreeSum.TernaryFrozenQueryStages.inverseDigit_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:23:41.948207+00:00
-- url     : https://prove2.me/submissions/4663d5ec-b085-46df-8ae6-5acb37a83956

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
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


attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryFrozenQueryStages
theorem _root_.solution (f : Fin 3→ℤ) (B : ℤ) (hf : ∀ d, |f d|≤B) (q : Fin 3) :
    |inverseDigit f q|≤4*B := by
  have hB : 0≤B := (abs_nonneg (f 0)).trans (hf 0)
  have hdiff (x y : ℤ) : |x-y|≤|x|+|y| := by
    simpa [sub_eq_add_neg] using abs_add_le x (-y)
  unfold inverseDigit
  split_ifs
  · exact (hf 0).trans (by omega)
  · exact (hdiff (f 1) (f 0)).trans (by linarith [hf 0,hf 1])
  · have hm : |2*f 1|≤2*B := by
      rw [abs_mul]
      norm_num
      linarith [hf 1]
    calc
      |f 2-2*f 1+f 0|≤|f 2-2*f 1|+|f 0| := abs_add_le _ _
      _≤(|f 2|+|2*f 1|)+|f 0| := add_le_add (hdiff _ _) le_rfl
      _≤4*B := by linarith [hf 0,hf 2]
end ThreeSum.TernaryFrozenQueryStages
