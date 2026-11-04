-- Prove2me | solution 1 for ThreeSum.TernaryQuery.coordinateInverse_coordinateZeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:11.331237+00:00
-- url     : https://prove2.me/submissions/6efd59c4-62fb-478c-ba60-ecf1fe603fdd

import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Theorems.Thm_ThreeSum_TernaryQuery_inverseDigit_zetaDigit
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
    (f : TritWord N → ℤ) : coordinateInverse i (coordinateZeta i f) = f := by
  funext R
  unfold coordinateInverse coordinateZeta
  simp only [Function.update_self, Function.update_idem]
  rw [inverseDigit_zetaDigit]
  simp
end ThreeSum.TernaryQuery
