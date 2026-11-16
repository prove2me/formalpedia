-- Prove2me | solution 1 for PHIP1891.negative_survives
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:56:12.599203+00:00
-- url     : https://prove2.me/submissions/2e22990c-0849-4d18-915b-ff18016ff84e

import Mathlib
open MeasureTheory Set

theorem solution (v w e d : ℝ)
    (hd : 0 < d) (hv : v ≤ -d) (herr : |w-v| ≤ e)
    (he : e < d) : w < 0 := by
  have h := (abs_le.mp herr).2
  linarith
