-- Prove2me | solution 1 for actuarial_e_spouse_due_after_spouse_death
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:16:26.346219+00:00
-- url     : https://prove2.me/submissions/263c5c53-54ae-4dad-9fee-b028002b0b5e

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

theorem solution (i j t : ℕ) (ht : j < t) : spouseDue i j t = 0 := by
  simp only [ActuarialDeathE.spouseDue, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
