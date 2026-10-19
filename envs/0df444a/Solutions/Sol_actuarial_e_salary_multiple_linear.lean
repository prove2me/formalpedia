-- Prove2me | solution 1 for actuarial_e_salary_multiple_linear
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:18:11.521165+00:00
-- url     : https://prove2.me/submissions/cc20705b-2bba-4ded-9886-2cd61e547c7f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_salaryMultiple

open ActuarialDeathE

theorem solution (salary : ℕ → ℝ) (t : ℕ) (k1 k2 : ℝ) : salaryMultiple (k1 + k2) salary t = salaryMultiple k1 salary t + salaryMultiple k2 salary t := by
  unfold salaryMultiple
  ring
