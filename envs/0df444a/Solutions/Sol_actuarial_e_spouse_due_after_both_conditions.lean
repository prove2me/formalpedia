-- Prove2me | solution 1 for actuarial_e_spouse_due_after_both_conditions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:09:51.527875+00:00
-- url     : https://prove2.me/submissions/44f92fe1-e6c4-4019-b866-2c5b0fb4d8d4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spouseDue

open ActuarialDeathE

theorem solution (i j t : ℕ) (hi : i + 1 < t) (hj : t ≤ j) : spouseDue i j t = 1 := by
  simp only [ActuarialDeathE.spouseDue, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
