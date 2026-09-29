-- Prove2me | solution 1 for WorkbookSource.base_1581
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:49.615303+00:00
-- url     : https://prove2.me/submissions/a07f35e6-097d-4464-b6fb-09f1ef366697

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : 3 * (x ^ 4 + y ^ 4 + z ^ 4) + 7 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 - (x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y)) ≥ 9 * (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x - (x * y ^ 3 + y * z ^ 3 + z * x ^ 3))  := by
  have h0 : 0 ≤ (3549/362 : ℝ) * (90319*x^2/1550913 - 214666*x*y/516971 - 214666*x*z/516971 - 543*y^2/1183 + y*z + 543*z^2/1183)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (663532569855/81781710374 : ℝ) * (387406115137*x^2/663532569855 - 214666*x*y/302305 + x*z - 106122625669*y^2/663532569855 - 79097*z^2/243879)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (192359805129/47822837170 : ℝ) * (-42999419393*x^2/192359805129 + x*y + 81776256301*y^2/192359805129 + 27303885295*z^2/192359805129)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (37781531/168122469682746 : ℝ) * (-3913372385*x^2/13676914222 - 3913372385*y^2/13676914222 + z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (4484370189313/21734197257673151208 : ℝ) * (-3913372385*x^2/9763541837 + y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (401225287/2316800606043567 : ℝ) * (x^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (x y z : ℝ), 3 * (x ^ 4 + y ^ 4 + z ^ 4) + 7 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 - (x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y)) ≥ 9 * (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x - (x * y ^ 3 + y * z ^ 3 + z * x ^ 3))) := @solution
#print axioms solution
