-- Prove2me | solution 1 for W1.differentiable
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:51:02.867513+00:00
-- url     : https://prove2.me/submissions/b863d8a6-9951-4ee2-a218-0adf2e6030b9

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
open W1

theorem solution (f : W1 (n + 1) E) : Differentiable ℝ f := by
  exact f.smooth.differentiable (by simp)
