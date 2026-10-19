-- Prove2me | solution 1 for actuarial_e_deferred_refund_disabled
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:17:33.668801+00:00
-- url     : https://prove2.me/submissions/bbf21b16-3288-49cc-808b-4b78a104e11b

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

theorem solution (atExit : ℝ) (growth capitalFactor refund : ℕ → ℝ) (t : ℕ) : deferredBundle atExit growth capitalFactor refund false t = revaluedDeferred atExit growth t * capitalFactor t := by
  simp [ActuarialDeathE.deferredBundle, ActuarialDeathE.revaluedDeferred, ActuarialJointD.alive, ActuarialJointD.dead, ActuarialJointD.expect, ActuarialJointD.mass, ActuarialJointD.onlyY, ActuarialJointD.valid]
