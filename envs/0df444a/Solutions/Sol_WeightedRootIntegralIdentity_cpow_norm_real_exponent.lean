-- Prove2me | solution 1 for WeightedRootIntegralIdentity.cpow_norm_real_exponent
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T08:27:51.734182+00:00
-- url     : https://prove2.me/submissions/2a28dd3b-13db-49c6-b3c8-e1d4b7871fc5

import Mathlib

theorem solution (b w ε : ℝ) :
    ‖((b : ℂ) + ε * Complex.I) ^ (w : ℂ)‖ =
      ‖(b : ℂ) + ε * Complex.I‖ ^ w := by
  simpa using Complex.norm_cpow_real ((b : ℂ) + ε * Complex.I) w
