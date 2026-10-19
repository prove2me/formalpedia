-- Prove2me | solution 1 for actuarial_e_member_after_death
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:07:57.895869+00:00
-- url     : https://prove2.me/submissions/b5e90ccd-a161-44d2-a4fa-d9365c92f1fe

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_memberPayment

open ActuarialDeathE

theorem solution (r i t : ℕ) (base : ℕ → ℝ) (hi : i < t) : memberPayment r i t base = 0 := by
  simp only [ActuarialDeathE.alive, ActuarialDeathE.memberPayment, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
