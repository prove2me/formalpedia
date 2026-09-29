-- Prove2me | solution 1 for WorkbookSource.base_41959
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:20.045098+00:00
-- url     : https://prove2.me/submissions/98cd9634-cede-4b1d-bdfa-9aea8c34f2b9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution {a b c : ℝ} : 22 * (a^6 + b^6 + c^6) - 36 * (a^5 * (b + c) + b^5 * (a + c) + c^5 * (a + b)) + 657 * (a^4 * (b^2 + c^2) + b^4 * (a^2 + c^2) + c^4 * (a^2 + b^2)) - 420 * (a^4 * b * c + b^4 * a * c + c^4 * a * b) - 28 * (a^3 * b^3 + b^3 * c^3 + c^3 * a^3) - 540 * (a^3 * b * c * (b + c) + b^3 * a * c * (a + c) + c^3 * a * b * (a + b)) + 792 * a^2 * b^2 * c^2 ≥ 0  := by
  have h0 : 0 ≤ (4447/9 : ℝ) * (-571*a^3/4447 + 1188*a^2*b/4447 - 1859*a^2*c/4447 - 1859*a*b^2/4447 - 1890*a*c^2/4447 + 733*b^3/4447 - 27*b^2*c/4447 + b*c^2 - 162*c^3/4447)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (19775080/40023 : ℝ) * (-571*a^3/4420 - 8234897*a^2*b/19775080 + 5232843*a^2*c/19775080 - 8455023*a*b^2/19775080 - 8318003*a*c^2/19775080 - 700623*b^3/19775080 + b^2*c + 3255277*c^3/19775080)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (22138163251/59325240 : ℝ) * (-4917735794*a^3/66414489753 - 258898383*a^2*b/962528837 + a^2*c - 611311217*a*b^2/962528837 - 92319237*a*c^2/962528837 - 4407670613*b^3/66414489753 + 9325406407*c^3/66414489753)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (999589784453/2887586511 : ℝ) * (-1099181*a^3/10851699 + a^2*b - 79461*a*b^2/276341 - 196880*a*c^2/276341 + 13661976709*b^3/103405839771 - 138603520*c^3/4495906077)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (38216853/276341 : ℝ) * (-a*b^2 + a*c^2 - 20416*b^3/471813 + 20416*c^3/471813)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (990400/97665291 : ℝ) * (-a^3/2 - b^3/2 + c^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h6 : 0 ≤ (247600/32555097 : ℝ) * (-a^3 + b^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6]
example : (∀ {a b c : ℝ}, 22 * (a^6 + b^6 + c^6) - 36 * (a^5 * (b + c) + b^5 * (a + c) + c^5 * (a + b)) + 657 * (a^4 * (b^2 + c^2) + b^4 * (a^2 + c^2) + c^4 * (a^2 + b^2)) - 420 * (a^4 * b * c + b^4 * a * c + c^4 * a * b) - 28 * (a^3 * b^3 + b^3 * c^3 + c^3 * a^3) - 540 * (a^3 * b * c * (b + c) + b^3 * a * c * (a + c) + c^3 * a * b * (a + b)) + 792 * a^2 * b^2 * c^2 ≥ 0) := @solution
#print axioms solution
