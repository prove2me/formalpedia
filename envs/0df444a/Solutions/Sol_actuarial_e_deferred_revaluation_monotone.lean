-- Prove2me | solution 1 for actuarial_e_deferred_revaluation_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:05:56.351916+00:00
-- url     : https://prove2.me/submissions/a9b56c6b-093f-416d-9dcf-d4e10bb1e711

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

theorem solution (atExit : ℝ) (growth : ℕ → ℝ) (t u : ℕ) (hp : 0 ≤ atExit) (hu : growth t ≤ growth u) : revaluedDeferred atExit growth t ≤ revaluedDeferred atExit growth u := by
  unfold revaluedDeferred
  exact mul_le_mul_of_nonneg_left hu hp
