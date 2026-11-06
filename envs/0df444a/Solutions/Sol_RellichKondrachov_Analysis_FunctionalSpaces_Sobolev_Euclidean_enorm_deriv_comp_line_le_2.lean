-- Prove2me | solution 2 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.enorm_deriv_comp_line_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:09.111654+00:00
-- url     : https://prove2.me/submissions/998d9e59-5275-446d-9805-cf005e8bc392

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_deriv_comp_line
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_enorm_fderiv_apply_le_enorm_grad_mul

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
variable [CompleteSpace E]
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
theorem _root_.solution (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ‖deriv (fun t => f (line (x := x) (a := a) t)) t‖ₑ ≤
      ‖a‖ₑ * ‖grad (E := E) f (line (x := x) (a := a) t)‖ₑ := by
  -- Reduce to the `fderiv` bound.
  have :=
    enorm_fderiv_apply_le_enorm_grad_mul
      (E := E) (f := f) (x := line (x := x) (a := a) t) (a := a)
  -- Rewrite `deriv` and commute the product.
  simpa [deriv_comp_line (hf := hf) (x := x) (a := a) t,
    mul_comm, mul_left_comm, mul_assoc] using this
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
