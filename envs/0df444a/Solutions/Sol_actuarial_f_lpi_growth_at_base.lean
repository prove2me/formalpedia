-- Prove2me | solution 1 for actuarial_f_lpi_growth_at_base
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:40:02.808204+00:00
-- url     : https://prove2.me/submissions/3981d8c1-8909-46bb-99f6-33d21c71e49e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiGrowth

open ActuarialUnderpinsF

theorem solution (floor cap : ℝ)
    (inflation : ℕ → ℝ) : lpiGrowth floor cap inflation 0 = 1 := by
  simp [lpiGrowth, compoundGrowth]
