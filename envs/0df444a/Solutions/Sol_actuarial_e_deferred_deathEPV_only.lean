-- Prove2me | solution 1 for actuarial_e_deferred_deathEPV_only
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:15:21.816948+00:00
-- url     : https://prove2.me/submissions/1568a4f0-9642-4b16-a1fd-9ecacf9857e9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_expect
import Definitions.Def_actuarial_e_deferred
import Definitions.Def_actuarial_e_deathEPV

open ActuarialDeathE

theorem solution (h e r : ℕ) (p : ℕ → ℕ → ℝ) (disc deferredBenefit : ℕ → ℝ) : deathEPV h e r p disc (fun t => 0) deferredBenefit (fun t => 0) = expect h p (fun i j => disc (i + 1) * deferred h e r i * deferredBenefit (i + 1)) := by
  simp [ActuarialDeathE.active, ActuarialDeathE.deathEPV, ActuarialDeathE.deathPV, ActuarialDeathE.deferred, ActuarialDeathE.expect, ActuarialDeathE.regimeLump, ActuarialDeathE.retired, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]
