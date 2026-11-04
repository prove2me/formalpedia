-- Prove2me | solution 1 for ThreeSum.TernaryBankEnumeration.wordList_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:28.616361+00:00
-- url     : https://prove2.me/submissions/4a460130-d4f2-42dd-b153-93afbac5b992

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryBankEnumeration
theorem _root_.solution (N : ℕ) : Function.Injective (@wordList N) := by
  intro w v h
  funext i
  apply Fin.ext
  have hh := congrArg (fun l : List ℕ => l[i.val]?) h
  simpa [wordList, i.isLt] using hh
end ThreeSum.TernaryBankEnumeration
