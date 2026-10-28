-- Prove2me | solution 1 for actuarial_f_spouse_fixed_base_above_first
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:37:33.684803+00:00
-- url     : https://prove2.me/submissions/972d58db-cab7-440a-8513-55aefa925133

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseBaseAtDeath

open ActuarialUnderpinsF

theorem solution (z i : ℕ)
    (a b : ℕ → ℕ → ℝ) :
    a z i ≤ spouseBaseAtDeath z i a b := by
  exact le_max_left _ _
