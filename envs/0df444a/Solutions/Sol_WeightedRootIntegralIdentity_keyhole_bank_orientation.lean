-- Prove2me | solution 1 for WeightedRootIntegralIdentity.keyhole_bank_orientation
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T10:59:04.494462+00:00
-- url     : https://prove2.me/submissions/b829b6b9-f785-4c98-aec3-68e242dbc6fa

import Mathlib
open scoped Interval

theorem solution {f : ℝ → ℂ} {a b : ℝ} :
    (∫ x in b..a, f x) = - ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_symm]
