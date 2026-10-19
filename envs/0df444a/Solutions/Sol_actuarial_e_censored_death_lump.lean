-- Prove2me | solution 1 for actuarial_e_censored_death_lump
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:11:59.76684+00:00
-- url     : https://prove2.me/submissions/4ff1382c-578f-4476-b9e4-07f4cbf7e1c9

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

theorem solution (h e r : ℕ) (service defer retire : ℕ → ℝ) : regimeLump h e r h service defer retire = 0 := by
  simp [ActuarialDeathE.active, ActuarialDeathE.deferred, ActuarialDeathE.regimeLump, ActuarialDeathE.retired, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]
