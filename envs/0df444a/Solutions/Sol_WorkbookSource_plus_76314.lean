-- Prove2me | solution 1 for WorkbookSource.plus_76314
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:27.885411+00:00
-- url     : https://prove2.me/submissions/ee307a6b-6c55-4e50-9f37-78edbbc4e105

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : (4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + (4 / 3) * ((a - c) ^ 2 + (b - d) ^ 2 + (c - a) ^ 2 + (d - b) ^ 2) + (8 / 3) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - a) ^ 2)) ^ 2 ≥ 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4)   := by
  have h0 : 0 ≤ (1792/9 : ℝ) * (-3*a^2/28 + a*b/7 - a*c/14 - a*d/14 - 3*b^2/28 - b*c/14 - b*d/14 - 9*c^2/28 + c*d - 9*d^2/28)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (4160/21 : ℝ) * (-3*a^2/26 - 4*a*b/65 + 9*a*c/65 - a*d/13 - 43*b^2/130 - b*c/13 + b*d - 17*c^2/130 - 9*d^2/26)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (2560/13 : ℝ) * (-a^2/8 - a*b/15 - a*c/15 + 2*a*d/15 - 43*b^2/120 + b*c - 43*c^2/120 - 19*d^2/120)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (8704/45 : ℝ) * (-45*a^2/136 - a*b/17 - a*c/17 + a*d - 13*b^2/136 - 13*c^2/136 - 49*d^2/136)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (16384/85 : ℝ) * (-45*a^2/128 - a*b/16 + a*c - 13*b^2/128 - 47*c^2/128 - 15*d^2/128)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (192 : ℝ) * (-3*a^2/8 + a*b - 3*b^2/8 - c^2/8 - d^2/8)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c d : ℝ), (4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + (4 / 3) * ((a - c) ^ 2 + (b - d) ^ 2 + (c - a) ^ 2 + (d - b) ^ 2) + (8 / 3) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - a) ^ 2)) ^ 2 ≥ 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4)) := @solution
#print axioms solution
