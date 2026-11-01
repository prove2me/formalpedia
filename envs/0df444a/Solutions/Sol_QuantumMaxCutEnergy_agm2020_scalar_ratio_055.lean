-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm2020_scalar_ratio_055
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T00:56:54.194199+00:00
-- url     : https://prove2.me/submissions/1518bdcc-9435-4984-8a21-7b3e8890d6f0

import Mathlib

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    (0.55 : ℝ) ≤
      max (2 * y) (max (3 * x + 1) ((4 + x + y) / 3)) / (2 + x + y) := by
  have hd : 0 < 2 + x + y := by linarith
  apply (le_div_iff₀ hd).2
  have h1 := le_max_left (2 * y) (max (3 * x + 1) ((4 + x + y) / 3))
  have h2 := (le_max_left (3 * x + 1) ((4 + x + y) / 3)).trans
    (le_max_right (2 * y) (max (3 * x + 1) ((4 + x + y) / 3)))
  have h3 := (le_max_right (3 * x + 1) ((4 + x + y) / 3)).trans
    (le_max_right (2 * y) (max (3 * x + 1) ((4 + x + y) / 3)))
  linarith

#print axioms solution
