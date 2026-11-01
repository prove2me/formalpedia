-- Prove2me | solution 1 for ParetoIneff.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T14:01:37.624313+00:00
-- url     : https://prove2.me/submissions/9caa9c43-18ff-4a19-a16a-baa2376da7d3

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

theorem solution (x y β γ : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hβ : 0 < β) (hγ : 0 < γ) :
    x + β * y ≤ (β / γ + 1) * max x (γ * y) := by
  have _ := hx
  have _ := hy
  have h1 : x ≤ max x (γ * y) := le_max_left x (γ * y)
  have h2 : γ * y ≤ max x (γ * y) := le_max_right x (γ * y)
  have h3 : β * y ≤ (β / γ) * max x (γ * y) := by
    have hbg : 0 ≤ β / γ := div_nonneg (le_of_lt hβ) (le_of_lt hγ)
    have hmul := mul_le_mul_of_nonneg_left h2 hbg
    have heq : (β / γ) * (γ * y) = β * y := by
      field_simp [ne_of_gt hγ]
    linarith
  linarith
