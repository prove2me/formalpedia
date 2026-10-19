-- Prove2me | solution 1 for actuarial_e_zero_cashflow_horizon
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:20:26.859595+00:00
-- url     : https://prove2.me/submissions/7aa4078f-bf7b-40fe-b6a0-cad0591c4d90

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_deathPV
import Definitions.Def_actuarial_e_realisedPV

open ActuarialDeathE

theorem solution (h e r g i j : ℕ) (disc service defer retire base a b c increase : ℕ → ℝ) (replace : Bool) : realisedPV h 0 e r g i j disc service defer retire base a b c increase replace = deathPV h e r i disc service defer retire := by
  simp only [ActuarialDeathE.active, ActuarialDeathE.alive, ActuarialDeathE.deathPV, ActuarialDeathE.deferred, ActuarialDeathE.guaranteePayment, ActuarialDeathE.instalment, ActuarialDeathE.memberPayment, ActuarialDeathE.realisedPV, ActuarialDeathE.regimeLump, ActuarialDeathE.retired, ActuarialDeathE.spouseDue, ActuarialDeathE.spousePayment, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
