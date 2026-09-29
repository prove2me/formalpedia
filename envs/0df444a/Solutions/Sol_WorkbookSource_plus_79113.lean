-- Prove2me | solution 1 for WorkbookSource.plus_79113
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:28.668323+00:00
-- url     : https://prove2.me/submissions/47a1b2d1-c3be-4502-a5ec-23b8711dcf43

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 + 4 * (a ^ 2 + d ^ 2) * (b ^ 2 + c ^ 2) ≥ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a + b + c + d) ^ 2   := by
  have h0 : 0 ≤ (414/97 : ℝ) * (-28*a^2/69 - 13*a*b/207 + 71*a*d/414 - 28*b^2/69 + 71*b*c/414 - 97*c^2/414 + c*d - 97*d^2/414)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (414/97 : ℝ) * (-28*a^2/69 - 13*a*c/207 + 71*a*d/414 - 97*b^2/414 + 71*b*c/414 + b*d - 28*c^2/69 - 97*d^2/414)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (880/207 : ℝ) * (-22263*a^2/85360 + a*c + 71*a*d/388 - 36037*b^2/85360 + 71*b*c/388 - 22263*c^2/85360 - 36037*d^2/85360)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (880/207 : ℝ) * (-22263*a^2/85360 + a*b + 71*a*d/388 - 22263*b^2/85360 + 71*b*c/388 - 36037*c^2/85360 - 36037*d^2/85360)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (66193/4139960 : ℝ) * (-65533*a^2/66193 - 660*a*d/66193 + 330*b^2/66193 - 660*b*c/66193 + 330*c^2/66193 + d^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (465661/29124920 : ℝ) * (660*a^2/66523 - 660*a*d/66523 - 65863*b^2/66523 - 660*b*c/66523 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h6 : 0 ≤ (21/66523 : ℝ) * (-a^2 + a*d - b^2 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6]
example : (∀ (a b c d : ℝ), 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 + 4 * (a ^ 2 + d ^ 2) * (b ^ 2 + c ^ 2) ≥ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a + b + c + d) ^ 2) := @solution
#print axioms solution
