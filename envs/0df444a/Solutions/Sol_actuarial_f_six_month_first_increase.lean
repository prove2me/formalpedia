-- Prove2me | solution 1 for actuarial_f_six_month_first_increase
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:13.915143+00:00
-- url     : https://prove2.me/submissions/98ede04a-fc98-4417-8ea9-7b55da532a46

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyScheduledRate

open ActuarialUnderpinsF

theorem solution :
    monthlyScheduledRate 0 6 0 (5 / 100)
      (fun _ => (4 / 100 : ℝ)) 6 = (2 / 100 : ℝ) := by
  have h1 : lpiRate 0 (5/100:ℝ) (4/100) = 4/100 := by
    unfold lpiRate
    rw [max_eq_right (by grind), min_eq_right (by grind)]
  have h2 : completeMonths 0 6 = 6 := by unfold completeMonths; decide
  unfold monthlyScheduledRate proratedAnnualRate
  dsimp only
  rw [if_pos ⟨by omega, rfl⟩, h1, h2]
  norm_num <;> grind
