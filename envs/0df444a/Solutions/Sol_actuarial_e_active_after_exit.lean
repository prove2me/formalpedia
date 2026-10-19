-- Prove2me | solution 1 for actuarial_e_active_after_exit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:10:36.917593+00:00
-- url     : https://prove2.me/submissions/3bfa0e13-9b13-4c5e-8f21-e0e1a3f19bb1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_active

open ActuarialDeathE

theorem solution (h e i : ℕ) (hi : e ≤ i) : active h e i = 0 := by
  simp only [ActuarialDeathE.active, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
