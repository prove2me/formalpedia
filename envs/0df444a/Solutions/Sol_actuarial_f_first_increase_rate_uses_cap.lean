-- Prove2me | solution 1 for actuarial_f_first_increase_rate_uses_cap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:35.406532+00:00
-- url     : https://prove2.me/submissions/a38d860a-73a5-45ae-9f7a-5c0b026e7bab

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate
import Definitions.Def_actuarial_f_completeMonths
import Definitions.Def_actuarial_f_proratedAnnualRate
import Definitions.Def_actuarial_f_monthlyScheduledRate

open ActuarialUnderpinsF

theorem solution
    (r first : ℕ) (floor cap observed : ℝ)
    (inflation : ℕ → ℝ) (hfirst : r < first)
    (hi : inflation 0 = observed) :
    monthlyScheduledRate r first floor cap inflation first =
      proratedAnnualRate (lpiRate floor cap observed)
        (completeMonths r first) := by
  unfold monthlyScheduledRate
  rw [if_pos ⟨hfirst, rfl⟩, hi]
