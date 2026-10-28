-- Prove2me | solution 1 for actuarial_f_post1988_gmp_three_percent_cap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:56:45.07717+00:00
-- url     : https://prove2.me/submissions/86d11010-3bab-43ee-9c9d-3cb2c9972fa0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_post88GmpIllustrativeRate

open ActuarialUnderpinsF



theorem solution :
    post88GmpIllustrativeRate (6 / 100) = (3 / 100 : ℝ) := by
  norm_num [post88GmpIllustrativeRate, lpiRate]
