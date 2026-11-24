-- Prove2me | solution 1 for VpVnp.separation_over_real
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:55:05.120137+00:00
-- url     : https://prove2.me/submissions/a084af46-e208-4eef-be7b-5a900bea7be9

import Theorems.Thm_VpVnp_separation

/-! Corollary of the all-fields circuit lower bound of Claude (Anthropic), *VP ≠ VNP over every field*,
https://hexagonmath.org/2611.00954v1 . -/

open VpVnp

theorem solution : VP ℝ ⊂ VNP ℝ := by
  exact VpVnp.separation ℝ
