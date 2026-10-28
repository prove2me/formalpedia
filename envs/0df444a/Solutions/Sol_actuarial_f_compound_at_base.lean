-- Prove2me | solution 1 for actuarial_f_compound_at_base
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:47.616457+00:00
-- url     : https://prove2.me/submissions/0814ea94-c263-450f-93f4-7a6bbd916816

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_compoundGrowth

open ActuarialUnderpinsF

theorem solution (r : ℕ → ℝ) :
    compoundGrowth r 0 = 1 := by
  simp [compoundGrowth]
