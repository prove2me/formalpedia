-- Prove2me | solution 2 for W1.differentiable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:17:00.255615+00:00
-- url     : https://prove2.me/submissions/880d4f76-199f-406c-87df-a28b47d29aa7

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
namespace W1
theorem _root_.solution (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)
end W1
