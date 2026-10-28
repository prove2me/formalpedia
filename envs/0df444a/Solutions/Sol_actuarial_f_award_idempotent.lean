-- Prove2me | solution 1 for actuarial_f_award_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:42.059211+00:00
-- url     : https://prove2.me/submissions/f2e3b8c4-06f0-4724-b74b-e0e1cbe46b0b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase

open ActuarialUnderpinsF

theorem solution (a : ℕ → ℝ) (z : ℕ) :
    awardBase a a z = a z := by
  exact max_self _
