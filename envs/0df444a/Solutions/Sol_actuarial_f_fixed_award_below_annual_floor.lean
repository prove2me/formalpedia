-- Prove2me | solution 1 for actuarial_f_fixed_award_below_annual_floor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:36:29.679657+00:00
-- url     : https://prove2.me/submissions/8a1f6d2e-d560-4c78-86d6-46e98f5bf81f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_annualFloorPayment
import Definitions.Def_actuarial_f_fixedChoicePayment

open ActuarialUnderpinsF

theorem solution (a b ga gb : ℕ → ℝ)
    (z t : ℕ) :
    fixedChoicePayment a b ga gb z t ≤ annualFloorPayment a b ga gb z t := by
  unfold fixedChoicePayment annualFloorPayment
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _
