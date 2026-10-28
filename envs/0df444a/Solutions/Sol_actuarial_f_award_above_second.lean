-- Prove2me | solution 1 for actuarial_f_award_above_second
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:34.09228+00:00
-- url     : https://prove2.me/submissions/07383b28-9450-47ee-a276-0037de8c1ad9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase

open ActuarialUnderpinsF

theorem solution (a b : ℕ → ℝ) (z : ℕ) :
    b z ≤ awardBase a b z := by
  exact le_max_right _ _
