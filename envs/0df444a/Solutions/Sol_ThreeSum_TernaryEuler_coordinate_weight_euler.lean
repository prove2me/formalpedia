-- Prove2me | solution 1 for ThreeSum.TernaryEuler.coordinate_weight_euler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:14.846235+00:00
-- url     : https://prove2.me/submissions/9c83046b-906f-4b8a-a3ba-f363f51a58d7

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Theorems.Thm_ThreeSum_TernaryEuler_digit_euler
import Theorems.Thm_ThreeSum_TernaryEuler_weight_split
import Theorems.Thm_ThreeSum_TernaryEuler_predecessor_weight

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryEuler
theorem _root_.solution {N : ℕ} (R A : TritWord N) (i : Fin N) :
    (R i).val * weight (predecessor R i) A =
      ((R i).val - (A i).val : ℤ) * weight R A := by
  rw [predecessor_weight, weight_split R A i, ← mul_assoc, digit_euler]
  ring
end ThreeSum.TernaryEuler
