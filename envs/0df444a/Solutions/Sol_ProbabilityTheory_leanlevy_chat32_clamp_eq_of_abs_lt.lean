-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat32_clamp_eq_of_abs_lt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:47:13.602556+00:00
-- url     : https://prove2.me/submissions/7c5ef807-b548-448d-8514-22c9bdf7e088

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_continuous
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_norm_le_crude
import Mathlib.Algebra.Order.Group.Unbundled.Abs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution {r x : ℝ} (hx : |x| < r) : max (-r) (min x r) = x := by
  obtain ⟨hxl, hxr⟩ := abs_lt.mp hx
  rw [min_eq_left (le_of_lt hxr), max_eq_right (le_of_lt hxl)]
