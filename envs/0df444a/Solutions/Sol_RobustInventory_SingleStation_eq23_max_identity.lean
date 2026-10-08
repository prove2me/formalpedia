-- Prove2me | solution 1 for RobustInventory.SingleStation.eq23_max_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:45:46.44167+00:00
-- url     : https://prove2.me/submissions/dc04a67d-8e94-4cee-a60b-a57539b838e7

import Mathlib

theorem solution (h p xbar A : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (hph : 0 < p + h) :
    max (h * (xbar + A)) (p * (-xbar + A)) =
      max (h * (xbar - (p - h) / (p + h) * A)) (-(p * (xbar - (p - h) / (p + h) * A)))
        + 2 * p * h / (p + h) * A := by
  have hne : p + h ≠ 0 := ne_of_gt hph
  have e1 : h * (xbar + A) = h * (xbar - (p - h) / (p + h) * A) + 2 * p * h / (p + h) * A := by
    field_simp
    ring
  have e2 : p * (-xbar + A) = -(p * (xbar - (p - h) / (p + h) * A)) + 2 * p * h / (p + h) * A := by
    field_simp
    ring
  rw [← max_add_add_right, ← e1, ← e2]

