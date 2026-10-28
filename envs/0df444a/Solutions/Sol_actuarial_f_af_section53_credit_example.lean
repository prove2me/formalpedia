-- Prove2me | solution 1 for actuarial_f_af_section53_credit_example
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:51:50.064835+00:00
-- url     : https://prove2.me/submissions/489e153a-765f-4ec6-a7c8-14a43d65bbdf

import Mathlib
import Definitions.Def_actuarial_f_afSection53StillPayable
open ActuarialUnderpinsF

theorem solution :
    afSection53StillPayable (3 / 100 : ℝ) (1 / 100) =
      (2 / 100 : ℝ) := by
  unfold afSection53StillPayable; norm_num
