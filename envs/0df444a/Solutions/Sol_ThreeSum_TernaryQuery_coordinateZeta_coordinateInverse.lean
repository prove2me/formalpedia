-- Prove2me | solution 1 for ThreeSum.TernaryQuery.coordinateZeta_coordinateInverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:12.572943+00:00
-- url     : https://prove2.me/submissions/3d3918ca-1c07-4243-b7cf-1b5cbc45b7c5

import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Theorems.Thm_ThreeSum_TernaryQuery_zetaDigit_inverseDigit
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
theorem _root_.solution {N : ℕ} (i : Fin N)
    (f : TritWord N → ℤ) : coordinateZeta i (coordinateInverse i f) = f := by
  funext R
  unfold coordinateZeta coordinateInverse
  simp only [Function.update_self, Function.update_idem]
  rw [zetaDigit_inverseDigit]
  simp
end ThreeSum.TernaryQuery
