-- Prove2me | solution 1 for RegLearnGames.FirstOrder.root_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:00:27.649978+00:00
-- url     : https://prove2.me/submissions/7f909656-05ca-45fa-9d73-3ab4d6b8f1cb

import Mathlib

set_option autoImplicit false

theorem solution (mu b cq x : ℝ)
    (hmu₀ : 0 < mu) (hmu₁ : mu < 1) (hx : 0 ≤ x)
    (hquad : (1 - mu) / mu * x ^ 2 + b * x + cq ≤ 0) :
    x ≤ mu / (2 * (1 - mu)) *
        (-b + Real.sqrt (b ^ 2 - 4 * ((1 - mu) / mu) * cq)) ∧
      mu / (2 * (1 - mu)) *
        (-b + Real.sqrt (b ^ 2 - 4 * ((1 - mu) / mu) * cq)) ≤
          mu / (1 - mu) *
            Real.sqrt (b ^ 2 - 2 * ((1 - mu) / mu) * cq) := by
  have h1mu : 0 < 1 - mu := by linarith
  have ha : 0 < (1 - mu) / mu := div_pos h1mu hmu₀
  have h1 : mu / (2 * (1 - mu)) = 1 / (2 * ((1 - mu) / mu)) := by
    field_simp
  have h2 : mu / (1 - mu) = 1 / ((1 - mu) / mu) := by
    field_simp
  rw [h1, h2]
  generalize (1 - mu) / mu = a at hquad ha ⊢
  have hD : 0 ≤ b ^ 2 - 4 * a * cq := by
    nlinarith [sq_nonneg (2 * a * x + b), mul_le_mul_of_nonneg_left hquad ha.le]
  set s := Real.sqrt (b ^ 2 - 4 * a * cq) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = b ^ 2 - 4 * a * cq := Real.sq_sqrt hD
  have hE : 0 ≤ b ^ 2 - 2 * a * cq := by nlinarith [sq_nonneg b]
  set r := Real.sqrt (b ^ 2 - 2 * a * cq) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = b ^ 2 - 2 * a * cq := Real.sq_sqrt hE
  have hxs : 2 * a * x + b ≤ s := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul_of_nonneg_left hquad ha.le]
  have hsr : -b + s ≤ 2 * r := by
    by_contra hc
    push_neg at hc
    nlinarith [sq_nonneg (s + b)]
  have h2a : 0 < 2 * a := by linarith
  constructor
  · rw [one_div, ← div_eq_inv_mul, le_div_iff₀ h2a]
    nlinarith
  · rw [one_div, ← div_eq_inv_mul, div_le_iff₀ h2a, one_div, ← div_eq_inv_mul, div_mul_eq_mul_div, le_div_iff₀ ha]
    nlinarith
