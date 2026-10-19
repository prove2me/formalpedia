-- Prove2me | solution 1 for PereiraGuimaraesElko.friedmann_eq_2_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:14:52.973975+00:00
-- url     : https://prove2.me/submissions/fb995fab-b548-47ae-a2e2-573c304c0db4

import Mathlib

theorem solution (κ H h Φ Φdot V : ℝ)
    (h25 : h = -(1 / 8) * (κ ^ 2 * Φ ^ 2 / (1 + κ ^ 2 * Φ ^ 2 / 8)) * H) :
    H ^ 2 = κ ^ 2 / 3 * (Φdot ^ 2 / 2 + V + 3 / 8 * H ^ 2 * Φ ^ 2 + 3 / 4 * H * h * Φ ^ 2)
        + (1 + κ ^ 2 * Φ ^ 2 / 8) * h ^ 2 ↔
      H ^ 2 = κ ^ 2 / 3 * (1 + κ ^ 2 * Φ ^ 2 / 8) * (Φdot ^ 2 / 2 + V) := by
  set D := 1 + κ ^ 2 * Φ ^ 2 / 8 with hD
  have hD0 : 0 < D := by positivity
  have hh : h * D = -(D - 1) * H := by rw [h25]; field_simp; ring
  have key : (κ ^ 2 / 3 * (Φdot ^ 2 / 2 + V + 3 / 8 * H ^ 2 * Φ ^ 2 + 3 / 4 * H * h * Φ ^ 2)
        + D * h ^ 2 - H ^ 2) * D = κ ^ 2 / 3 * D * (Φdot ^ 2 / 2 + V) - H ^ 2 := by
    have e : κ ^ 2 * Φ ^ 2 = 8 * (D - 1) := by rw [hD]; ring
    linear_combination (κ ^ 2 / 4 * Φ ^ 2 * H + D * h - (D - 1) * H) * hh + (1/8 * H^2 * D + 1/4 * H * h * D) * e
  constructor
  · intro h1
    have : (κ ^ 2 / 3 * (Φdot ^ 2 / 2 + V + 3 / 8 * H ^ 2 * Φ ^ 2 + 3 / 4 * H * h * Φ ^ 2)
        + D * h ^ 2 - H ^ 2) = 0 := by linarith
    rw [this, zero_mul] at key; linarith
  · intro h1
    have : (κ ^ 2 / 3 * (Φdot ^ 2 / 2 + V + 3 / 8 * H ^ 2 * Φ ^ 2 + 3 / 4 * H * h * Φ ^ 2)
        + D * h ^ 2 - H ^ 2) * D = 0 := by linarith
    rcases mul_eq_zero.mp this with h2 | h2
    · linarith
    · exact absurd h2 hD0.ne'
