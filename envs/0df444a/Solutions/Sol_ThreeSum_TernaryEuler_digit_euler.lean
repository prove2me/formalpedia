-- Prove2me | solution 1 for ThreeSum.TernaryEuler.digit_euler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:37.089203+00:00
-- url     : https://prove2.me/submissions/27e8006c-7da1-47cc-afb3-89db2dcd810b

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryEuler
theorem _root_.solution (r a : Fin 3) :
    (r.val : ℤ) * digitChoose (predDigit r) a =
      ((r.val : ℤ) - (a.val : ℤ)) * digitChoose r a := by
  fin_cases r <;> fin_cases a <;> norm_num [digitChoose, predDigit, Nat.choose]
end ThreeSum.TernaryEuler
