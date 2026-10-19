-- Prove2me | solution 1 for RhinViola.unitIntervalOneSubPowIntegral
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:26:41.481882+00:00
-- url     : https://prove2.me/submissions/5a8b868c-a611-4934-9eeb-3d14c0e60a9b

import Mathlib

set_option autoImplicit false

theorem solution (n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, (1 - x) ^ n) =
      (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) (1 : ℝ)]
  simp [integral_pow]
