-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.enorm_deriv_comp_line_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:03:24.546197+00:00
-- url     : https://prove2.me/submissions/9bac6651-4dd7-4627-bb96-cc06c36d9051

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate
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

theorem solution (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ‖deriv (fun t => f (line (x := x) (a := a) t)) t‖ₑ ≤
      ‖a‖ₑ * ‖grad (E := E) f (line (x := x) (a := a) t)‖ₑ := by
  have hline : HasDerivAt (line (x := x) (a := a)) a t := by
    have hsmul : HasDerivAt (fun t : ℝ => t • a) a t := by
      simpa [one_smul] using! (hasDerivAt_id t).smul_const a
    exact HasDerivAt.const_add x hsmul
  have hf' : HasFDerivAt f (fderiv ℝ f (line (x := x) (a := a) t))
      (line (x := x) (a := a) t) :=
    (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hcomp :
      HasDerivAt (fun t => f (line (x := x) (a := a) t))
        (fderiv ℝ f (line (x := x) (a := a) t) a) t :=
    HasFDerivAt.comp_hasDerivAt_of_eq t hf' hline rfl
  rw [hcomp.deriv]
  have h₁ :
      ‖fderiv ℝ f (line (x := x) (a := a) t) a‖ₑ ≤
        ‖fderiv ℝ f (line (x := x) (a := a) t)‖ₑ * ‖a‖ₑ :=
    (ContinuousLinearMap.le_opNorm_enorm
      (f := fderiv ℝ f (line (x := x) (a := a) t)) a)
  have h₂ : ‖grad (E := E) f (line (x := x) (a := a) t)‖ₑ =
      ‖fderiv ℝ f (line (x := x) (a := a) t)‖ₑ := by
    simpa [grad] using!
      (LinearIsometry.enorm_map
        (f := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry)
        (fderiv ℝ f (line (x := x) (a := a) t)))
  simpa [h₂, mul_comm] using h₁
