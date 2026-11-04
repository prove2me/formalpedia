-- Prove2me | solution 1 for ThreeSum.TernaryBank.digit_deficit_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:35:18.529209+00:00
-- url     : https://prove2.me/submissions/b66f392d-2c35-4ce1-80f2-8d98e5322992

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution (z : ℝ) (q : Fin 3) :
    (∑ r : Fin 3, digitDeficitWeight z q r) =
      if q = 0 then 1 else if q = 1 then 1 + z else 1 + z + z ^ 2 := by
  fin_cases q <;> norm_num [digitDeficitWeight, Fin.sum_univ_succ, Fin.le_def] <;> ring
end ThreeSum.TernaryBank
