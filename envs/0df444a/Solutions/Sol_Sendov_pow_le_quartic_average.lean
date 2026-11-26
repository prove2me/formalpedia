-- Prove2me | solution 1 for Sendov.pow_le_quartic_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:06:05.202738+00:00
-- url     : https://prove2.me/submissions/d79c2bf9-b423-4d15-baba-91cb24b67e01

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm0 : 1 ≤ m) (hm4 : m ≤ 4) :
    x ^ m ≤ 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * x ^ 4 := by
  interval_cases m
  · -- `m = 1`:  `X⁴ - 4X + 3 = (X-1)²(X² + 2X + 3)`
    have hpos : (0 : ℝ) ≤ x ^ 2 + 2 * x + 3 := by positivity
    norm_num
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) hpos]
  · -- `m = 2`:  `X⁴ - 2X² + 1 = (X² - 1)²`
    norm_num
    nlinarith [sq_nonneg (x ^ 2 - 1)]
  · -- `m = 3`:  `3X⁴ - 4X³ + 1 = (X-1)²(3X² + 2X + 1)`
    have hpos : (0 : ℝ) ≤ 3 * x ^ 2 + 2 * x + 1 := by positivity
    norm_num
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) hpos]
  · -- `m = 4`: equality
    norm_num
end Sendov
