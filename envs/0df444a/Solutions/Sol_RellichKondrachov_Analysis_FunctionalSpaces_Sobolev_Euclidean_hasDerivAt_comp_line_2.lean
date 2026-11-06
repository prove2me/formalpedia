-- Prove2me | solution 2 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.hasDerivAt_comp_line
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:37:52.311475+00:00
-- url     : https://prove2.me/submissions/a63560c2-b5bd-4f55-968b-799fc754b941

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_hasDerivAt_line

set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceTranslationEstimate
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceTranslationEstimate
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceTranslationEstimate
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
theorem _root_.solution
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    HasDerivAt (fun t => f (line (x := x) (a := a) t))
      (fderiv ℝ f (line (x := x) (a := a) t) a) t := by
  have hf' : HasFDerivAt f (fderiv ℝ f (line (x := x) (a := a) t)) (line (x := x) (a := a) t) :=
    (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  exact
    HasFDerivAt.comp_hasDerivAt_of_eq t hf' (hasDerivAt_line (x := x) (a := a) t) rfl
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
