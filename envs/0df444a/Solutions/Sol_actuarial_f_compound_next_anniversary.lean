-- Prove2me | solution 1 for actuarial_f_compound_next_anniversary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:52.112043+00:00
-- url     : https://prove2.me/submissions/b1d08d5e-4e96-46df-a7eb-a27f51e0e0a1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_compoundGrowth

open ActuarialUnderpinsF

theorem solution (r : ℕ → ℝ) (t : ℕ) :
    compoundGrowth r (t+1) = compoundGrowth r t * (1+r t) := by
  simp [compoundGrowth, Finset.prod_range_succ]
