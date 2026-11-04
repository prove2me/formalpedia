-- Prove2me | solution 1 for ThreeSum.TernaryNearBankEnumeration.wordList_deficit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:33.118866+00:00
-- url     : https://prove2.me/submissions/b35e4329-1bcc-457b-8752-6ff8a50a8950

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
namespace ThreeSum.TernaryNearBankEnumeration
theorem _root_.solution {N : ℕ} (Q R : TritWord N) :
    (List.zipWith Nat.sub (wordList Q) (wordList R)).sum = deficit Q R := by
  have hzip : List.zipWith Nat.sub (wordList Q) (wordList R) =
      List.ofFn (fun i : Fin N => (Q i).val-(R i).val) := by
    apply List.ext_getElem
    · simp [wordList]
    · intro i hi hj
      simp [wordList,List.getElem_zipWith]
  rw [hzip]
  simp [deficit,List.sum_ofFn]
end ThreeSum.TernaryNearBankEnumeration
