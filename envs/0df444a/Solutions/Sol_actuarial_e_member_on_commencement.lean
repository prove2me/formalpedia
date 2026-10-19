-- Prove2me | solution 1 for actuarial_e_member_on_commencement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:08:17.305412+00:00
-- url     : https://prove2.me/submissions/0b5df039-7d1c-479d-b435-46a96f1b0b5d

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

theorem solution (r i : ℕ) (base : ℕ → ℝ) (hr : r ≤ i) : memberPayment r i r base = base r := by
  simp only [ActuarialDeathE.alive, ActuarialDeathE.memberPayment, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
