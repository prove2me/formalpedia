-- Prove2me | solution 1 for WorkbookSource.base_80
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:36:19.670403+00:00
-- url     : https://prove2.me/submissions/b6662f0e-2144-47a7-b28d-9fe6f01fc2c5

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) : |a - b| + |b - c| + |c - a| + a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 + (4:ℝ) / 3  := by
  rcases le_total (a-b) 0 with hab | hab <;>
  rcases le_total (b-c) 0 with hbc | hbc <;>
  rcases le_total (c-a) 0 with hca | hca <;>
  simp only [abs_of_nonpos, abs_of_nonneg, *] <;>
  nlinarith [sq_nonneg (3*(a-b)-4),sq_nonneg (3*(a-b)+4),sq_nonneg (3*(b-c)-4),sq_nonneg (3*(b-c)+4),sq_nonneg (3*(c-a)-4),sq_nonneg (3*(c-a)+4),sq_nonneg (2*a-b-c),sq_nonneg (2*b-c-a),sq_nonneg (2*c-a-b)]
example : (∀ (a b c : ℝ), |a - b| + |b - c| + |c - a| + a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 + (4:ℝ) / 3) := @solution
#print axioms solution
