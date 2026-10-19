-- Prove2me | solution 1 for actuarial_e_deathPV_zero_rate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:12:35.555497+00:00
-- url     : https://prove2.me/submissions/b21770b8-d319-4805-8405-919542fc6e62

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_regimeLump
import Definitions.Def_actuarial_e_deathPV

open ActuarialDeathE

theorem solution (h e r i : ℕ) (service defer retire : ℕ → ℝ) : deathPV h e r i (fun t => (1 : ℝ)) service defer retire = regimeLump h e r i service defer retire := by
  simp [ActuarialDeathE.active, ActuarialDeathE.deathPV, ActuarialDeathE.deferred, ActuarialDeathE.regimeLump, ActuarialDeathE.retired, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]
