-- Prove2me | solution 1 for WorkbookSource.base_37001
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:14.734773+00:00
-- url     : https://prove2.me/submissions/16a43f2e-79c3-41d4-9894-7ebb65703e34

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) :
  3 * (a^2 * b + a * b^2 + b^2 * c + b * c^2 + c^2 * a + c * a^2)^2 ≤
  4 * (a^2 + b^2 + c^2)^3  := by
  have h0 : 0 ≤ (29/7 : ℝ) * (-17*a^3/29 + 7*a^2*b/29 - 4*a^2*c/29 - 4*a*b^2/29 - 21*a*c^2/29 + 17*b^3/29 - 7*b^2*c/29 + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (825/203 : ℝ) * (17*a^3/33 - 7*a^2*b/33 - 4*a^2*c/25 + a*b^2 + 119*a*c^2/825 + 68*b^3/825 - 637*b^2*c/825 - 493*c^3/825)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (99/25 : ℝ) * (-25*a^2*b/33 + a^2*c - a*c^2/3 - 17*b^3/33 + b^2*c/11 + 17*c^3/33)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (346/231 : ℝ) * (-a^3/2 - 323*a^2*b/346 + 119*a*c^2/173 - b^3/2 + 85*b^2*c/346 + c^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (469/346 : ℝ) * (-2941*a^3/3283 - 919*a^2*b/3283 - 2364*a*c^2/3283 + 2941*b^3/3283 + b^2*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (8996/252791 : ℝ) * (-a^3 + 85*a^2*b/346 - 85*a*c^2/346 + b^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h6 : 0 ≤ (39/1211 : ℝ) * (-a^2*b + a*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6]
example : (∀ (a b c : ℝ), 3 * (a^2 * b + a * b^2 + b^2 * c + b * c^2 + c^2 * a + c * a^2)^2 ≤
  4 * (a^2 + b^2 + c^2)^3) := @solution
#print axioms solution
