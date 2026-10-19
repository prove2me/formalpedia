-- Prove2me | solution 1 for actuarial_e_deferred_from_exit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:16:49.950908+00:00
-- url     : https://prove2.me/submissions/81f299ec-fbfa-4244-a4d7-6b96a0f0df93

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_deferred

open ActuarialDeathE

theorem solution (h e r i : ℕ) (hi : i < h) (hx : e ≤ i) (hr : i < r) : deferred h e r i = 1 := by
  simp only [ActuarialDeathE.deferred, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
