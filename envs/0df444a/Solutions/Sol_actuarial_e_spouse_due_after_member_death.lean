-- Prove2me | solution 1 for actuarial_e_spouse_due_after_member_death
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:16:02.283934+00:00
-- url     : https://prove2.me/submissions/2f092100-2a43-45e7-b8a6-67e52dc15872

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

theorem solution (i j t : ℕ) (ht : t ≤ i + 1) : spouseDue i j t = 0 := by
  simp only [ActuarialDeathE.spouseDue, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
