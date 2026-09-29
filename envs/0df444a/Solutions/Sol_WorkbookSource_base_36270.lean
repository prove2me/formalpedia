-- Prove2me | solution 1 for WorkbookSource.base_36270
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:11.360566+00:00
-- url     : https://prove2.me/submissions/14904ce0-b03d-43a2-8e49-e1f5a155e935

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) + (a + b + c - d) * (a + b + d - c) * (a + c + d - b) * (b + c + d - a) ≥ 8 * a * b * c * d + (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)  := by
  have h0 : 0 ≤ (32/27 : ℝ) * (-5*a^2/8 - 9*a*b/16 + 13*a*c/64 + 13*a*d/64 - 5*b^2/8 + 13*b*c/64 + 13*b*d/64 + c*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1309/1152 : ℝ) * (-40*a^2/77 + 1300*a*b/3927 - 2473*a*c/3927 + 13*a*d/77 + 520*b^2/3927 + 13*b*c/77 + b*d - 2560*c^2/3927)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (85/77 : ℝ) * (-4*a^2/9 + 130*a*b/459 + 130*a*c/459 - 311*a*d/459 + 52*b^2/459 + b*c + 52*c^2/459 - 308*d^2/459)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (7400/12393 : ℝ) * (-51*a^2/370 + 65*a*b/74 + 65*a*c/74 + a*d - 329*b^2/370 - 329*c^2/370 - 311*d^2/370)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (6950/50949 : ℝ) * (-51*a^2/695 + 65*a*b/139 + a*c - 329*b^2/695 - 181*c^2/695 - 459*d^2/695)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (400/3753 : ℝ) * (-a^2/20 + a*b - b^2/20 - 9*c^2/20 - 9*d^2/20)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c d : ℝ), 2 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) + (a + b + c - d) * (a + b + d - c) * (a + c + d - b) * (b + c + d - a) ≥ 8 * a * b * c * d + (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)) := @solution
#print axioms solution
