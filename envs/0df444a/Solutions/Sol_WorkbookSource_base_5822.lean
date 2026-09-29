-- Prove2me | solution 1 for WorkbookSource.base_5822
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:41:00.391679+00:00
-- url     : https://prove2.me/submissions/d83f3d1f-ac48-4742-afc8-c066f039dac8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution  (a b c : ℝ) :
  (a + b)^2 * (a + c)^2 ≥ 4 * a * b * c * (a + b + c)  := by
  have h0 : 0 ≤ (1 : ℝ) * (-a^2 - a*b - a*c + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0]
example : (∀ (a b c : ℝ), (a + b)^2 * (a + c)^2 ≥ 4 * a * b * c * (a + b + c)) := @solution
#print axioms solution
