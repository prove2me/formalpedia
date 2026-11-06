-- Prove2me | solution 1 for W21.hf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:33:54.111586+00:00
-- url     : https://prove2.me/submissions/1d2b648f-d819-44e9-98ec-cebc4ad6e9ab

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev

set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
open W21
variable {f : W21}
namespace W21
theorem _root_.solution (f : W21) : Integrable f := f.integrable zero_le_two
end W21
