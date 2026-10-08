-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_integrand_dominated_bound
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T09:05:29.003475+00:00
-- url     : https://prove2.me/submissions/a88e5423-8a2b-4931-958e-ad281c14a39f

import Mathlib

theorem solution {z w : ℂ} {N δ : ℝ}
    (hN : ‖z‖ ≤ N) (hδ : 0 < δ) (hden : δ ≤ ‖w‖) :
    ‖z / w‖ ≤ N / δ := by
  rw [norm_div]
  have hN0 : 0 ≤ N := le_trans (norm_nonneg z) hN
  gcongr
