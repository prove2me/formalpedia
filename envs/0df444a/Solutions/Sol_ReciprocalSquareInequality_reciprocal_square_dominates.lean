-- Prove2me | solution 1 for ReciprocalSquareInequality.reciprocal_square_dominates
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-13T12:05:11.89866+00:00
-- url     : https://prove2.me/submissions/d4d740f2-56e1-42b7-92e4-5b88de8c0948

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 2) :
    1 / a ^ 2 + 1 / b ^ 2 ≥ a ^ 2 + b ^ 2 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hp : 0 < a * b := mul_pos ha hb
  have hp_le : a * b ≤ 1 := by
    nlinarith [sq_nonneg (a - b)]
  have hden_pos : 0 < a ^ 2 * b ^ 2 := by positivity
  have hden_le : a ^ 2 * b ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hp_le)]
  have hsum_nonneg : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hmul : (a ^ 2 + b ^ 2) * (a ^ 2 * b ^ 2) ≤ a ^ 2 + b ^ 2 :=
    mul_le_of_le_one_right hsum_nonneg hden_le
  have hfrac : a ^ 2 + b ^ 2 ≤ (a ^ 2 + b ^ 2) / (a ^ 2 * b ^ 2) :=
    (le_div_iff₀ hden_pos).2 hmul
  calc
    a ^ 2 + b ^ 2 ≤ (a ^ 2 + b ^ 2) / (a ^ 2 * b ^ 2) := hfrac
    _ = 1 / a ^ 2 + 1 / b ^ 2 := by field_simp [ha0, hb0] <;> ring
