-- Prove2me | solution 1 for actuarial_e_member_before_retirement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:08:07.675489+00:00
-- url     : https://prove2.me/submissions/4015b28b-6a6b-4e58-b0f7-3ecbe36e643c

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

theorem solution (r i t : ℕ) (base : ℕ → ℝ) (ht : t < r) : memberPayment r i t base = 0 := by
  simp only [ActuarialDeathE.alive, ActuarialDeathE.memberPayment, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
