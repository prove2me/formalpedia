-- Prove2me | solution 1 for actuarial_e_deferred_refund_enabled
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:18:20.930887+00:00
-- url     : https://prove2.me/submissions/66545ea2-20da-4aac-82e1-09205cb2125c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_revaluedDeferred
import Definitions.Def_actuarial_e_deferredBundle

open ActuarialDeathE

theorem solution (atExit : ℝ) (growth capitalFactor refund : ℕ → ℝ) (t : ℕ) : deferredBundle atExit growth capitalFactor refund true t = revaluedDeferred atExit growth t * capitalFactor t + refund t := by
  simp [ActuarialDeathE.deferredBundle, ActuarialDeathE.revaluedDeferred, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]
