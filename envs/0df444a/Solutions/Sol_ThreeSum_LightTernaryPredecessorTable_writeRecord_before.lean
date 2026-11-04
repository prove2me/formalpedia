-- Prove2me | solution 1 for ThreeSum.LightTernaryPredecessorTable.writeRecord_before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:19.916611+00:00
-- url     : https://prove2.me/submissions/c375e31b-5202-4565-a192-cc394682d2dd

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
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
open ThreeSum ThreeSum.LightTernaryPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ThreeSum.LightTernaryPredecessorTable
theorem _root_.solution {μ : ℕ → ℤ} {dst stride n j k N low high m T active bv nv bi ni : ℕ}
    {w z : ℤ} (hs : 0<stride) (hk : k<j) (hj : j<n)
    (H : RecordAt μ dst stride n k N low high m T active bv nv bi ni) :
    RecordAt (writeRecord μ dst stride n j w z) dst stride n k N low high m T active bv nv bi ni := by
  have hkj : stride*k<stride*j := Nat.mul_lt_mul_of_pos_left hk hs
  have hkn : stride*k<stride*n := Nat.mul_lt_mul_of_pos_left (by omega) hs
  have hjn : stride*j<stride*n := Nat.mul_lt_mul_of_pos_left hj hs
  unfold RecordAt writeRecord at *
  simp only [Function.update_of_ne (by omega : dst+stride*k≠dst+stride*n+stride*j),
    Function.update_of_ne (by omega : dst+stride*k≠dst+stride*j),
    Function.update_of_ne (by omega : dst+stride*n+stride*k≠dst+stride*n+stride*j),
    Function.update_of_ne (by omega : dst+stride*n+stride*k≠dst+stride*j)]
  exact H
end ThreeSum.LightTernaryPredecessorTable
