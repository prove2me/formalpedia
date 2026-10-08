-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_quotient_dominated_bound
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T08:54:13.042304+00:00
-- url     : https://prove2.me/submissions/ab360d11-c6cb-4201-8513-6bd0a2520ce0

import Mathlib

theorem solution {z w : ℂ} {N δ : ℝ}
    (hN : ‖z‖ ≤ N) (hδ : 0 < δ) (hden : δ ≤ ‖w‖) :
    ‖z / w‖ ≤ N / δ := by
  rw [norm_div]
  have hN0 : 0 ≤ N := le_trans (norm_nonneg z) hN
  gcongr
