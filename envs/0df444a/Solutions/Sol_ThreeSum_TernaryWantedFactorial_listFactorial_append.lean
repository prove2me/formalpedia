-- Prove2me | solution 1 for ThreeSum.TernaryWantedFactorial.listFactorial_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:18.559687+00:00
-- url     : https://prove2.me/submissions/532b8e4e-176e-4955-8169-5645f5e10dfc

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedFactorial
open TernaryJointType
set_option maxHeartbeats 1000000
namespace ThreeSum.TernaryWantedFactorial
theorem _root_.solution (xs ys : List ℕ) :
    listFactorial (xs++ys)=listFactorial xs*listFactorial ys := by
  simp [listFactorial]
end ThreeSum.TernaryWantedFactorial
