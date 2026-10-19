-- Prove2me | solution 1 for actuarial_e_deferred_before_exit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:14:41.832845+00:00
-- url     : https://prove2.me/submissions/d4c2cb05-8b91-4d43-8b1f-06185f9f92e2

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

theorem solution (h e r i : ℕ) (hi : i < e) : deferred h e r i = 0 := by
  simp only [ActuarialDeathE.deferred, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
