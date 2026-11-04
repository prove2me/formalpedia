-- Prove2me | solution 1 for ThreeSum.TernaryWantedFactorial.typed_blocks_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:09:29.365845+00:00
-- url     : https://prove2.me/submissions/02bf8b44-6bc3-413e-8c8a-978bccfe8f96

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
import Theorems.Thm_ThreeSum_TernaryWantedFactorial_listFactorial_append
import Theorems.Thm_ThreeSum_TernaryWantedFactorial_listFactorial_word
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryConvolution_factorial_eq_power_two
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
theorem _root_.solution {L : ℕ} (π : DigitType) (qs : List (TritWord L))
    (hq : ∀ q∈qs, HasType q π) :
    listFactorial (qs.flatMap TernaryBankEnumeration.wordList)=(2 : ℤ)^(qs.length*π 2) := by
  induction qs with
  | nil => simp [listFactorial]
  | cons q qs ih =>
    have hq0 := hq q (by simp)
    have hqs : ∀ q∈qs, HasType q π := by intro r hr; exact hq r (by simp [hr])
    simp only [List.flatMap_cons,listFactorial_append,listFactorial_word,
      TernaryConvolution.factorial_eq_power_two,hq0 2,ih hqs,List.length_cons]
    rw [Nat.add_mul,one_mul,pow_add]
    ring
end ThreeSum.TernaryWantedFactorial
