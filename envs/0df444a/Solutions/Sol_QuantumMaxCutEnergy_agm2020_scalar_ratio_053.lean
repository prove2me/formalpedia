-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm2020_scalar_ratio_053
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T00:56:56.811303+00:00
-- url     : https://prove2.me/submissions/f212a7b0-7fcd-4065-9148-4c89037d5592

import Mathlib

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    (0.53 : ℝ) ≤
      max (2 * y) (max (3 * x + 0.98) ((0.956 / 3) * (4 + x + y))) /
        (2 + x + y) := by
  have hd : 0 < 2 + x + y := by linarith
  apply (le_div_iff₀ hd).2
  have h1 := le_max_left (2 * y) (max (3 * x + 0.98) ((0.956 / 3) * (4 + x + y)))
  have h2 := (le_max_left (3 * x + 0.98) ((0.956 / 3) * (4 + x + y))).trans
    (le_max_right (2 * y) (max (3 * x + 0.98) ((0.956 / 3) * (4 + x + y))))
  have h3 := (le_max_right (3 * x + 0.98) ((0.956 / 3) * (4 + x + y))).trans
    (le_max_right (2 * y) (max (3 * x + 0.98) ((0.956 / 3) * (4 + x + y))))
  linarith

#print axioms solution
