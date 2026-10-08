-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_reciprocal_dominated_bound
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T09:02:21.467529+00:00
-- url     : https://prove2.me/submissions/a5bf7df2-36c7-437c-a847-637f225b4f0b

import Mathlib

theorem solution {x ε δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖((x : ℂ) + ε * Complex.I)⁻¹‖ ≤ δ⁻¹ := by
  rw [norm_inv]
  have hreal : x ≤ ‖(x : ℂ) + ε * Complex.I‖ := by
    simpa using (Complex.re_le_norm ((x : ℂ) + ε * Complex.I))
  have h : δ ≤ ‖(x : ℂ) + ε * Complex.I‖ := le_trans hx hreal
  gcongr
