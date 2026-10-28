-- Prove2me | solution 1 for actuarial_f_post2005_illustrative_two_half_cap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:51:12.888344+00:00
-- url     : https://prove2.me/submissions/bdadf29c-a4c6-4395-a9f4-8c853039312e

import Mathlib
import Definitions.Def_actuarial_f_post05IllustrativeRate
open ActuarialUnderpinsF

theorem solution :
    post05IllustrativeRate (8 / 100) = (25 / 1000 : ℝ) := by
  unfold post05IllustrativeRate lpiRate; norm_num
