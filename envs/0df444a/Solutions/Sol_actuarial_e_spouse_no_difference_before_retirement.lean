-- Prove2me | solution 1 for actuarial_e_spouse_no_difference_before_retirement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:19:35.27976+00:00
-- url     : https://prove2.me/submissions/51dca11b-27ad-44d2-9966-d368ed4e2114

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spousePayment

open ActuarialDeathE

theorem solution (h e r g i j t : ℕ) (a b c increase : ℕ → ℝ) (hi : i < r) : spousePayment h e r g i j t a b c increase false = spousePayment h e r g i j t a b c increase true := by
  simp only [ActuarialDeathE.active, ActuarialDeathE.deferred, ActuarialDeathE.retired, ActuarialDeathE.spouseDue, ActuarialDeathE.spousePayment, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
