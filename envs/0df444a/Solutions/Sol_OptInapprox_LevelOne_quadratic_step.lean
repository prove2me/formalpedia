-- Prove2me | solution 1 for OptInapprox.LevelOne.quadratic_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:03:44.955173+00:00
-- url     : https://prove2.me/submissions/fcc8b918-2437-461d-96b1-dd58f003dc9c

import Mathlib
set_option autoImplicit false

theorem solution (X δ : ℝ) (hX : 0 ≤ X) (hδ : 0 ≤ δ)
    (h : X ^ 2 ≤ Real.sqrt (2 / Real.pi) * X + (2 * (1 - Real.sqrt (2 / Real.pi)) / 2) * δ) :
    X ≤ Real.sqrt (1 / (2 * Real.pi)) +
        Real.sqrt (1 / (2 * Real.pi) + 2 * (1 - Real.sqrt (2 / Real.pi)) * δ / 2) ∧
    X ^ 2 ≤ 2 / Real.pi + 2 * (1 - Real.sqrt (2 / Real.pi)) * δ := by
  set a := Real.sqrt (2 / Real.pi) with ha
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 / Real.pi := by
    rw [ha, Real.sq_sqrt]; positivity
  have ha1 : a < 1 := by
    have : a ^ 2 < 1 := by
      rw [ha2, div_lt_one (by positivity)]; linarith
    nlinarith
  have hc : 0 ≤ (1 - a) * δ := mul_nonneg (by linarith) hδ
  have hq : 1 / (2 * Real.pi) = a ^ 2 / 4 := by
    rw [ha2]; field_simp; ring
  have hh : X ^ 2 ≤ a * X + (1 - a) * δ := by nlinarith
  set s := Real.sqrt (a ^ 2 / 4 + (1 - a) * δ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a ^ 2 / 4 + (1 - a) * δ := by
    rw [hs, Real.sq_sqrt]; positivity
  have hq2 : 1 / (2 * Real.pi) + 2 * (1 - a) * δ / 2 = a ^ 2 / 4 + (1 - a) * δ := by
    rw [hq]; ring
  have hsq : Real.sqrt (1 / (2 * Real.pi)) = a / 2 := by
    rw [hq, show a ^ 2 / 4 = (a / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsq, hq2, ← hs]
  have hX1 : X ≤ a / 2 + s := by
    nlinarith [sq_nonneg (X - a / 2 - s)]
  refine ⟨hX1, ?_⟩
  have : a * s ≤ a ^ 2 / 2 + (1 - a) * δ := by
    nlinarith [sq_nonneg (a / 2 - s)]
  rw [← ha2]
  nlinarith [mul_le_mul_of_nonneg_left hX1 ha0]
