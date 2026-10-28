-- Prove2me | solution 1 for actuarial_f_fixed_choice_at_award
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:40:40.559991+00:00
-- url     : https://prove2.me/submissions/28e2b589-b6af-4791-ab89-34e8f77f7269

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_fixedChoicePayment

open ActuarialUnderpinsF

theorem solution (a b : ℕ → ℝ) (z : ℕ) :
    fixedChoicePayment a b (fun _ => 1) (fun _ => 1) z 0 =
      awardBase a b z := by
  unfold fixedChoicePayment awardBase
  split_ifs with hab
  · simp [max_eq_right hab]
  · simp [max_eq_left (le_of_lt (not_le.mp hab))]
