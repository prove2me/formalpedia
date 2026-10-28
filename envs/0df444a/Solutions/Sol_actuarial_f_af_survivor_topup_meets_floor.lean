-- Prove2me | solution 1 for actuarial_f_af_survivor_topup_meets_floor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:00:30.40111+00:00
-- url     : https://prove2.me/submissions/0c49838e-17df-40e6-a2fe-e1f25743848e

import Mathlib
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_f_afStatutoryWeeklyToMonthly
import Definitions.Def_actuarial_f_afSurvivorSection87TopUp
open ActuarialUnderpinsF

theorem solution
    (h i j t : ℕ) (scheme weekly : ℝ)
    (hdue : spouseDue h i j t = 1) :
    afStatutoryWeeklyToMonthly weekly ≤
      scheme + afSurvivorSection87TopUp h i j t scheme weekly := by
  unfold afSurvivorSection87TopUp
  rw [hdue, mul_one]
  have := le_max_right 0 (afStatutoryWeeklyToMonthly weekly - scheme)
  linarith
