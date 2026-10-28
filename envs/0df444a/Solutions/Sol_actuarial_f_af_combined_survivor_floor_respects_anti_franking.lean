-- Prove2me | solution 1 for actuarial_f_af_combined_survivor_floor_respects_anti_franking
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:03:41.453864+00:00
-- url     : https://prove2.me/submissions/9cb14716-7e9e-4d1a-88fa-9ab5f51d1afe

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afStatutoryWeeklyToMonthly
import Definitions.Def_actuarial_f_afSurvivorCombinedMinimum

open ActuarialUnderpinsF



theorem solution
    (gmpMonthly antiFrankingWeekly : ℝ) :
    afStatutoryWeeklyToMonthly antiFrankingWeekly ≤
      afSurvivorCombinedMinimum gmpMonthly antiFrankingWeekly := by
  exact le_max_right _ _
