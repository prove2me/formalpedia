-- Prove2me | solution 1 for actuarial_f_af_weekly_monthly_conversion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:50:53.541785+00:00
-- url     : https://prove2.me/submissions/65c5d40f-ba03-4380-8f41-f90f4ef50cf6

import Mathlib
import Definitions.Def_actuarial_f_afStatutoryWeeklyToMonthly
open ActuarialUnderpinsF

theorem solution :
    afStatutoryWeeklyToMonthly 12 = (52 : ℝ) := by
  unfold afStatutoryWeeklyToMonthly; norm_num
