-- Prove2me | solution 1 for actuarial_f_monthly_growth_first_increase
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:32.214168+00:00
-- url     : https://prove2.me/submissions/e68b4f01-630b-4964-b6fb-22d6dc0a1aa4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate
import Definitions.Def_actuarial_f_completeMonths
import Definitions.Def_actuarial_f_proratedAnnualRate
import Definitions.Def_actuarial_f_monthlyScheduledGrowth

open ActuarialUnderpinsF

theorem solution
    (r first : ℕ) (floor cap : ℝ) (inflation : ℕ → ℝ)
    (hr : r < first) :
    monthlyScheduledGrowth r first floor cap inflation first =
      1 + proratedAnnualRate (lpiRate floor cap (inflation 0))
            (completeMonths r first) := by
  unfold monthlyScheduledGrowth
  rw [Finset.prod_range_succ, Finset.prod_eq_one]
  · unfold monthlyScheduledRate
    rw [if_pos ⟨hr, rfl⟩]
    grind
  · intro m hm
    rw [Finset.mem_range] at hm
    unfold monthlyScheduledRate
    rw [if_neg (by omega), if_neg (by omega)]
    grind
