-- Prove2me | solution 1 for actuarial_e_disjoint_active_deferred
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:19:03.165759+00:00
-- url     : https://prove2.me/submissions/b8076982-8254-4164-ad1c-a636009b7516

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_active
import Definitions.Def_actuarial_e_deferred

open ActuarialDeathE

theorem solution (h e r i : ℕ) (her : e ≤ r) : active h e i * deferred h e r i = 0 := by
  simp only [ActuarialDeathE.active, ActuarialDeathE.deferred, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
