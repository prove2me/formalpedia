-- Prove2me | solution 1 for WeightedRootIntegralIdentity.keyhole_arc_integrand_bound
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T10:40:46.517448+00:00
-- url     : https://prove2.me/submissions/9a896b80-33a3-4765-982f-b292ce61976e

import Mathlib

theorem solution {F : ℂ → ℂ} {z : ℂ} {M r : ℝ}
    (hF : ‖F z‖ ≤ M) (hr : 0 < r) (hz : ‖z‖ = r) :
    ‖F z / z‖ ≤ M / r := by
  rw [norm_div]
  have hM : 0 ≤ M := le_trans (norm_nonneg (F z)) hF
  rw [hz]
  gcongr
