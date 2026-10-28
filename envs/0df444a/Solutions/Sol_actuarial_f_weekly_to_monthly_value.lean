-- Prove2me | solution 1 for actuarial_f_weekly_to_monthly_value
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:50:22.405138+00:00
-- url     : https://prove2.me/submissions/649e16bf-b5ff-4610-944a-924e6da9c424

import Mathlib
import Definitions.Def_actuarial_f_weeklyGmpToMonthly
open ActuarialUnderpinsF

theorem solution :
    weeklyGmpToMonthly 12 = (52 : ℝ) := by
  unfold weeklyGmpToMonthly; norm_num
