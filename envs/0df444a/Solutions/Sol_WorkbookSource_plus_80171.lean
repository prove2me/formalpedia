-- Prove2me | solution 1 for WorkbookSource.plus_80171
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:44.780805+00:00
-- url     : https://prove2.me/submissions/b8d70ba7-8fd4-4025-a389-5624add187cc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≥ 2 * (a * b + b * c + c * a)   := by
  have h0 : 0 ≤ (1 : ℝ) * (-51*a*b/100 - 35*a*c/69 - b*c/2 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-5*a*b*c/86 - 34*a/69 - b/2 + c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (7371/7396 : ℝ) * (a*b*c - 128914*a/1525797 - 35303*b/449631)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (236905094/315839979 : ℝ) * (a - 1431458671581*b/1445121073400)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (3/4 : ℝ) * (-837*a*b/3050 - 2320*a*c/8901 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (18268592/26409267 : ℝ) * (-1654692933*a*b/4457536448 + a*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h6 : 0 ≤ (1199316739992647/2039322924960000 : ℝ) * (a*b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h7 : 0 ≤ (69572945904741/8815238547740000 : ℝ) * (b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7]
example : (∀ (a b c : ℝ), (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≥ 2 * (a * b + b * c + c * a)) := @solution
#print axioms solution
