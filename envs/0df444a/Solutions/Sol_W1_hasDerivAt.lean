-- Prove2me | solution 1 for W1.hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:25:07.128474+00:00
-- url     : https://prove2.me/submissions/54b99579-a306-455f-9273-c38aba081f39

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

theorem solution (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x := by
  change HasDerivAt f (_root_.deriv f x) x
  exact (f.smooth.differentiable (by simp) x).hasDerivAt
