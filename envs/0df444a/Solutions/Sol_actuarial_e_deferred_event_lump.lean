-- Prove2me | solution 1 for actuarial_e_deferred_event_lump
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:16:06.067653+00:00
-- url     : https://prove2.me/submissions/2a007443-05f3-4092-83f4-9fae15af9e8a

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

theorem solution (h e r i : ℕ) (service defer retire : ℕ → ℝ) (he : e ≤ r) (hi : i < h) (h1 : e ≤ i) (h2 : i < r) : regimeLump h e r i service defer retire = defer (i + 1) := by
  simp only [ActuarialDeathE.active, ActuarialDeathE.deferred, ActuarialDeathE.regimeLump, ActuarialDeathE.retired, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]; split_ifs <;> simp_all <;> linarith
