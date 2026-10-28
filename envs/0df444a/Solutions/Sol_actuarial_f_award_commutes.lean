-- Prove2me | solution 1 for actuarial_f_award_commutes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:38.149519+00:00
-- url     : https://prove2.me/submissions/19c98e6b-5e61-4054-ae2a-deb578804a19

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase

open ActuarialUnderpinsF

theorem solution (a b : ℕ → ℝ) (z : ℕ) :
    awardBase a b z = awardBase b a z := by
  exact max_comm _ _
