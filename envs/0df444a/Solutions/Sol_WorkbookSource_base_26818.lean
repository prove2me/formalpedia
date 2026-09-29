-- Prove2me | solution 1 for WorkbookSource.base_26818
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:47:44.159575+00:00
-- url     : https://prove2.me/submissions/befbaeb0-2b4a-4ba1-8969-c0397b87b6c6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a^2 + b^2 + c^2)^3 ≥ (a^3 + b^3 + c^3 + a * b * c)^2  := by
  have h0 : 0 ≤ (3 : ℝ) * (47*a^2*b/135 - a*c^2/3 - b^2*c/3 + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3 : ℝ) * (-a^2*b/3 + a*b^2 + 3*a*c^2/10 - b^2*c/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (3 : ℝ) * (-a^2*b/3 + a^2*c - a*c^2/3 + 5*b^2*c/27)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (542/243 : ℝ) * (243*a^2*b/2710 + 369*a*c^2/5420 + b^2*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (333817/162600 : ℝ) * (440774*a^2*b/3004353 + a*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (429830299/225326475 : ℝ) * (a^2*b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ), (a^2 + b^2 + c^2)^3 ≥ (a^3 + b^3 + c^3 + a * b * c)^2) := @solution
#print axioms solution
