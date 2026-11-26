-- Prove2me | solution 1 for closure_convexThickeningApprox_succ_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:27.401215+00:00
-- url     : https://prove2.me/submissions/cb63872b-f423-4f32-bfc6-c60f272e438c

import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution (K : Set ℂ) (n : ℕ) :
    closure (convexThickeningApprox K (n + 1)) ⊆
      convexThickeningApprox K n := by
  unfold convexThickeningApprox
  apply (Metric.closure_thickening_subset_cthickening
    (smoothApproxRadius (n + 1)) K).trans
  apply Metric.cthickening_subset_thickening'
  · exact smoothApproxRadius_pos n
  · unfold smoothApproxRadius
    exact Nat.one_div_lt_one_div (Nat.lt_succ_self n)
