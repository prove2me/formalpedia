-- Prove2me | solution 1 for ThreeSum.TernaryQuery.update_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:03:58.244494+00:00
-- url     : https://prove2.me/submissions/e9d630dd-3242-4270-a9df-f82c3fcb5905

import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryQuery
open ThreeSum.TernaryJointType
open ThreeSum.TernaryBank
namespace ThreeSum.TernaryQuery
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N) (d : Fin 3)
    (hd : d ≤ R i) : Below (Function.update R i d) R := by
  intro j
  by_cases h : j = i
  · subst j
    simpa using hd
  · simp [Function.update_of_ne h]
end ThreeSum.TernaryQuery
