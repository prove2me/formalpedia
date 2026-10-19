-- Prove2me | solution 1 for actuarial_e_service_event_lump
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:09:29.451598+00:00
-- url     : https://prove2.me/submissions/a0b2e13c-4b1c-4d09-aa63-eadbce94eb82

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_regimeLump

open ActuarialDeathE

theorem solution (h e r i : ℕ) (service defer retire : ℕ → ℝ) (her : e ≤ r) (hi : i < h) (he : i < e) : regimeLump h e r i service defer retire = service (i + 1) := by
  simp only [ActuarialDeathE.active, ActuarialDeathE.deferred, ActuarialDeathE.regimeLump, ActuarialDeathE.retired, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
