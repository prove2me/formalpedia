-- Prove2me | solution 1 for ThreeSum.TernaryQuery.runInverse_runZeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:23.009089+00:00
-- url     : https://prove2.me/submissions/d9d44ec4-780a-4b13-a30c-9dfdc33d777b

import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Theorems.Thm_ThreeSum_TernaryQuery_coordinateInverse_coordinateZeta
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
theorem _root_.solution {N : ℕ} (coords : List (Fin N)) (f : TritWord N → ℤ) :
    runInverse coords (runZeta coords f) = f := by
  induction coords with
  | nil => rfl
  | cons i rest ih =>
      simp only [runZeta, runInverse, coordinateInverse_coordinateZeta]
      exact ih
end ThreeSum.TernaryQuery
