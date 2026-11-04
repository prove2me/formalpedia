-- Prove2me | solution 1 for ThreeSum.TernaryWantedFactorial.factorial_of_canonical_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:08.652444+00:00
-- url     : https://prove2.me/submissions/1a26a643-6ac9-44f1-a3e4-ce56a3d4912c

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
import Theorems.Thm_ThreeSum_TernaryWantedFactorial_listFactorial_word
import Theorems.Thm_ThreeSum_TernaryWantedFactorial_typed_blocks_factorial
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
theorem _root_.solution {N L : ℕ} (Q : TritWord N) (π : DigitType)
    (qs : List (TritWord L)) (hq : ∀ q∈qs, HasType q π)
    (hword : TernaryBankEnumeration.wordList Q=qs.reverse.flatMap TernaryBankEnumeration.wordList) :
    TernaryConvolution.factorial Q=(2 : ℤ)^(qs.length*π 2) := by
  rw [← listFactorial_word,hword]
  have hh := typed_blocks_factorial π qs.reverse (by
    intro q hq'; exact hq q (List.mem_reverse.mp hq'))
  simpa using hh
end ThreeSum.TernaryWantedFactorial
