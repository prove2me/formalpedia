-- Prove2me | solution 1 for ThreeSum.TernaryQuery.zetaDigit_inverseDigit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:03:57.20996+00:00
-- url     : https://prove2.me/submissions/6228ab73-e4fa-4fe8-a140-0ac6f1527e08

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
theorem _root_.solution (f : Fin 3 → ℤ) :
    zetaDigit (inverseDigit f) = f := by
  funext d
  fin_cases d <;> simp [inverseDigit, zetaDigit,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] <;> ring
end ThreeSum.TernaryQuery
