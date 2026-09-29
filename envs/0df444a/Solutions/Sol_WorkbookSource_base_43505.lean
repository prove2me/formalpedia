-- Prove2me | solution 1 for WorkbookSource.base_43505
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:23.042029+00:00
-- url     : https://prove2.me/submissions/aa259658-696d-4481-96a2-1c5b3d6d778b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (2 * (b - c) ^ 2 + 2 * a ^ 2 + b * c) * (2 * (c - a) ^ 2 + 2 * b ^ 2 + c * a) * (2 * (a - b) ^ 2 + 2 * c ^ 2 + a * b) ≥ (a ^ 2 + b ^ 2 + c ^ 2) ^ 3  := by
  have h0 : 0 ≤ (35/4 : ℝ) * (-a^3/70 + 2*a^2*b/7 - 23*a^2*c/70 - 23*a*b^2/70 + 12*a*c^2/35 + 7*b^3/10 - 34*b^2*c/35 + b*c^2 - 24*c^3/35)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (225/28 : ℝ) * (-167*a^3/225 + a^2*b + 107*a^2*c/225 - 43*a*b^2/45 - 209*a*c^2/450 + 49*b^3/90 - b^2*c/18 + 89*c^3/450)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (21557/3600 : ℝ) * (12232*a^3/21557 - 20662*a^2*c/21557 - 290*a*b^2/21557 + a*c^2 - 695*b^3/21557 - 605*b^2*c/21557 - 11537*c^3/21557)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (369171/431140 : ℝ) * (-506735*a^3/738342 + 281197*a^2*c/738342 - 48671*a*b^2/67122 - 231607*b^3/738342 + 42364*b^2*c/123057 + c^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (1071193/2953368 : ℝ) * (814540*a^3/1071193 + a^2*c - 25993*a*b^2/1071193 - 814540*b^3/1071193 - 1045200*b^2*c/1071193)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (260139/8569544 : ℝ) * (-a^3 - 2856*a*b^2/7883 + b^3 + 2856*b^2*c/7883)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h6 : 0 ≤ (99/7883 : ℝ) * (-a*b^2 + b^2*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6]
example : (∀ (a b c : ℝ), (2 * (b - c) ^ 2 + 2 * a ^ 2 + b * c) * (2 * (c - a) ^ 2 + 2 * b ^ 2 + c * a) * (2 * (a - b) ^ 2 + 2 * c ^ 2 + a * b) ≥ (a ^ 2 + b ^ 2 + c ^ 2) ^ 3) := @solution
#print axioms solution
