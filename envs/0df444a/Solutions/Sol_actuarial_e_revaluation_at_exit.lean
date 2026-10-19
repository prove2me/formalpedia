-- Prove2me | solution 1 for actuarial_e_revaluation_at_exit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:18:03.92543+00:00
-- url     : https://prove2.me/submissions/7a4326eb-f89e-4f2c-a227-1feed4570e79

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_revaluedDeferred

open ActuarialDeathE

theorem solution (atExit : ℝ) (growth : ℕ → ℝ) (t : ℕ) (h : growth t = 1) : revaluedDeferred atExit growth t = atExit := by
  unfold revaluedDeferred
  rw [h, mul_one]
