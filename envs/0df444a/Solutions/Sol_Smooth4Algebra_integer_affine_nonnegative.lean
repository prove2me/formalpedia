-- Prove2me | solution 1 for Smooth4Algebra.integer_affine_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T06:01:45.736706+00:00
-- url     : https://prove2.me/submissions/64c508f3-e284-4c24-a13a-74f94bfa3c7a

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
set_option autoImplicit false

theorem solution
    (a b : ℝ) (h : ∀ n : ℤ, 0 ≤ a + (n : ℝ) * b) : b = 0 := by
  by_contra hb
  rcases lt_or_gt_of_ne hb with hb | hb
  · obtain ⟨n, hn⟩ := exists_int_gt (a / (-b))
    have ht : a < (n : ℝ) * (-b) := (div_lt_iff₀ (neg_pos.mpr hb)).mp hn
    have hh := h n
    nlinarith
  · obtain ⟨n, hn⟩ := exists_int_gt (a / b)
    have ht : a < (n : ℝ) * b := (div_lt_iff₀ hb).mp hn
    have hh := h (-n)
    push_cast at hh
    nlinarith

