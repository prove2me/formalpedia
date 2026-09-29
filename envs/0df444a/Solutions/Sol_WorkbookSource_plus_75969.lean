-- Prove2me | solution 1 for WorkbookSource.plus_75969
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:27.169172+00:00
-- url     : https://prove2.me/submissions/8aecaba2-d2df-47ee-997b-e9d794a525b1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : a + b + c + (1 / 4) * (a - c) ^ 2 + (1 / 2) * (3 - a ^ 2 - b ^ 2 - c ^ 2) ≤ 3   := by
  have h0 : 0 ≤ (3/2 : ℝ) * (-a/3 - b/3 - c/3 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1/3 : ℝ) * (-a/2 + b - c/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c : ℝ), a + b + c + (1 / 4) * (a - c) ^ 2 + (1 / 2) * (3 - a ^ 2 - b ^ 2 - c ^ 2) ≤ 3) := @solution
#print axioms solution
