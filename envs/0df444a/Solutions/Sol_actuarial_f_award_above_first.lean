-- Prove2me | solution 1 for actuarial_f_award_above_first
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:29.34599+00:00
-- url     : https://prove2.me/submissions/66985d83-b1da-4b93-aff8-553d0c600631

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase

open ActuarialUnderpinsF

theorem solution (a b : ℕ → ℝ) (z : ℕ) :
    a z ≤ awardBase a b z := by
  exact le_max_left _ _
