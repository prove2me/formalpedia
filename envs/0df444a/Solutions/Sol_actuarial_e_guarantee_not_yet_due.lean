-- Prove2me | solution 1 for actuarial_e_guarantee_not_yet_due
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:07:47.939144+00:00
-- url     : https://prove2.me/submissions/34ccf00b-86e9-4847-985a-fd247a38f4b7

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_guaranteePayment

open ActuarialDeathE

theorem solution (h r g i t : ℕ) (base : ℕ → ℝ) (ht : t ≤ i) : guaranteePayment h r g i t base = 0 := by
  simp only [ActuarialDeathE.guaranteePayment, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> first | rfl | simp_all | omega | linarith
