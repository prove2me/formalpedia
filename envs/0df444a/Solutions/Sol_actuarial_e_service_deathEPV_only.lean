-- Prove2me | solution 1 for actuarial_e_service_deathEPV_only
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:09:21.565512+00:00
-- url     : https://prove2.me/submissions/c5f32496-1fe2-42b5-bad1-1fad45e5927c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_expect
import Definitions.Def_actuarial_e_active
import Definitions.Def_actuarial_e_deathEPV

open ActuarialDeathE

theorem solution (h e r : ℕ) (p : ℕ → ℕ → ℝ) (disc service : ℕ → ℝ) : deathEPV h e r p disc service (fun t => 0) (fun t => 0) = expect h p (fun i j => disc (i + 1) * active h e i * service (i + 1)) := by
  simp only [ActuarialDeathE.active, ActuarialDeathE.deathEPV, ActuarialDeathE.deathPV, ActuarialDeathE.deferred, ActuarialDeathE.expect, ActuarialDeathE.regimeLump, ActuarialDeathE.retired, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
