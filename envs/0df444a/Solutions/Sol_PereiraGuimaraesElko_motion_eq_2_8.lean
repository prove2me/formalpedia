-- Prove2me | solution 1 for PereiraGuimaraesElko.motion_eq_2_8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:15:00.023883+00:00
-- url     : https://prove2.me/submissions/f4bc5917-9418-457f-b606-21ef12e394c8

import Mathlib

theorem solution (κ H h Φ Φdot Φddot dV : ℝ)
    (h25 : h = -(1 / 8) * (κ ^ 2 * Φ ^ 2 / (1 + κ ^ 2 * Φ ^ 2 / 8)) * H) :
    Φddot + 3 * H * Φdot + dV - 3 / 4 * (H + h) ^ 2 * Φ = 0 ↔
      Φddot + 3 * H * Φdot + dV - 3 / 4 * (H ^ 2 * Φ) / (1 + κ ^ 2 * Φ ^ 2 / 8) ^ 2 = 0 := by
  have hD0 : 0 < 1 + κ ^ 2 * Φ ^ 2 / 8 := by positivity
  have e : (H + h) ^ 2 * Φ = H ^ 2 * Φ / (1 + κ ^ 2 * Φ ^ 2 / 8) ^ 2 := by
    rw [h25]; field_simp; ring
  rw [show 3 / 4 * (H + h) ^ 2 * Φ = 3 / 4 * (H ^ 2 * Φ) / (1 + κ ^ 2 * Φ ^ 2 / 8) ^ 2 by
    rw [mul_assoc, e]; ring]
