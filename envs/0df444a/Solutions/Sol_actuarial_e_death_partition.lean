-- Prove2me | solution 1 for actuarial_e_death_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:14:02.871366+00:00
-- url     : https://prove2.me/submissions/ea402e29-604c-4d50-ad6e-3556322136ff

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
import Definitions.Def_actuarial_e_retired

open ActuarialDeathE

theorem solution (h e r i : ℕ) (her : e ≤ r) (hi : i < h) : active h e i + deferred h e r i + retired h r i = 1 := by
  simp only [ActuarialDeathE.active, ActuarialDeathE.deferred, ActuarialDeathE.retired, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
