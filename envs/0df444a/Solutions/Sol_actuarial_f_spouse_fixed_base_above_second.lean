-- Prove2me | solution 1 for actuarial_f_spouse_fixed_base_above_second
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:37:37.514245+00:00
-- url     : https://prove2.me/submissions/8251c834-f4e1-40f3-9250-d94ee7c198ef

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseBaseAtDeath

open ActuarialUnderpinsF

theorem solution (z i : ℕ)
    (a b : ℕ → ℕ → ℝ) :
    b z i ≤ spouseBaseAtDeath z i a b := by
  exact le_max_right _ _
