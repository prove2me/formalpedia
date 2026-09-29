-- Prove2me | solution 1 for WorkbookSource.base_9
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:36:18.970996+00:00
-- url     : https://prove2.me/submissions/c3b9fb58-60ed-4659-9e57-52a9d0d4599e

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b : ℝ) : (a * b + 1) - Real.sqrt (1 + a ^ 2 * b ^ 2) ≤ 2  := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 1+a^2*b^2 by positivity)
  have hp := Real.sqrt_nonneg (1+a^2*b^2)
  have : a*b ≤ Real.sqrt (1+a^2*b^2) := by nlinarith [sq_nonneg (a*b + Real.sqrt (1+a^2*b^2))]
  linarith
example : (∀ (a b : ℝ), (a * b + 1) - Real.sqrt (1 + a ^ 2 * b ^ 2) ≤ 2) := @solution
#print axioms solution
