-- Prove2me | solution 1 for SubsetShrink.L2.eq_34
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T12:14:26.215642+00:00
-- url     : https://prove2.me/submissions/3e034a72-d1ea-44f8-8dc7-27a393544f51

import Mathlib
set_option autoImplicit false

theorem solution (α a b : ℝ) (hα : 0 < α) :
    2 * a * b ≤ α * a ^ 2 + α⁻¹ * b ^ 2 := by
  have h : 0 ≤ α⁻¹ * (α * a - b) ^ 2 := by positivity
  have e : α⁻¹ * (α * a - b) ^ 2 = α * a ^ 2 - 2 * a * b + α⁻¹ * b ^ 2 := by
    field_simp
    ring
  linarith
