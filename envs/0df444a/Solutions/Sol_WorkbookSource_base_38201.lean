-- Prove2me | solution 1 for WorkbookSource.base_38201
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:17.886695+00:00
-- url     : https://prove2.me/submissions/eb396a48-ce1d-468d-a489-64e8a8e840c0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 4 * (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ 3 * (a * b + b * c + c * a) * (a + b + c)  := by
  have h0 : 0 ≤ (4 : ℝ) * (-a*b*c/40 - a*b/40 - a*c/40 - b*c/40 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (4 : ℝ) * (-5*a*b*c/36 - 3*a*b/8 - 3*a*c/8 + a/40 - 3*b*c/8 + b/40 + c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1599/400 : ℝ) * (-2200*a*b*c/14391 - 15*a*b/41 - 545*a*c/1599 + a/41 - 15*b*c/41 + b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (819/205 : ℝ) * (-7775*a*b*c/58968 - 5*a*b/14 - 293*a*c/819 + a - 5*b*c/14)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (398826119/106142400 : ℝ) * (a*b*c - 66077856*a*b/398826119 - 64489356*a*c/398826119 - 66077856*b*c/398826119)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (75331528601/31906089520 : ℝ) * (-321336677395*a*b/677983757409 + a*c - 321336677395*b*c/677983757409)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h6 : 0 ≤ (10719959959238/6101853816681 : ℝ) * (-78990373376483*a*b/85759679673904 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h7 : 0 ≤ (182771270030367/686077437391232 : ℝ) * (a*b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7]
example : (∀ (a b c : ℝ), 4 * (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ 3 * (a * b + b * c + c * a) * (a + b + c)) := @solution
#print axioms solution
