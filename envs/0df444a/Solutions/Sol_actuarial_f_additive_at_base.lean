-- Prove2me | solution 1 for actuarial_f_additive_at_base
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:01.430103+00:00
-- url     : https://prove2.me/submissions/36e6476c-6f0d-44ab-b4e9-5236ba9c317a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_additiveGrowth

open ActuarialUnderpinsF

theorem solution (r : ℕ → ℝ) :
    additiveGrowth r 0 = 1 := by
  simp [additiveGrowth]
