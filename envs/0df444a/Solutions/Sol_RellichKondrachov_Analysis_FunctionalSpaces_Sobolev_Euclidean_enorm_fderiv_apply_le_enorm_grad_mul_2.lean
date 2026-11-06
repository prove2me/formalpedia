-- Prove2me | solution 2 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.enorm_fderiv_apply_le_enorm_grad_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:37:55.876596+00:00
-- url     : https://prove2.me/submissions/9a609622-ba9c-4cd6-998a-ec637db35082

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
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
theorem _root_.solution (f : E → ℝ) (x a : E) :
    ‖fderiv ℝ f x a‖ₑ ≤ ‖grad (E := E) f x‖ₑ * ‖a‖ₑ := by
  -- Use the operator norm bound, then identify `‖fderiv‖` with `‖grad‖` via the Riesz isometry.
  have h₁ :
      ‖fderiv ℝ f x a‖ₑ ≤ ‖fderiv ℝ f x‖ₑ * ‖a‖ₑ :=
    (ContinuousLinearMap.le_opENorm (f := fderiv ℝ f x) a)
  have h₂ : ‖grad (E := E) f x‖ₑ = ‖fderiv ℝ f x‖ₑ := by
    -- `grad f x = (toDual).symm (fderiv f x)` and `toDual.symm` is an isometry.
    simp only [grad]
    exact
      (LinearIsometry.enorm_map
        (f := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry)
        (fderiv ℝ f x))
  -- Replace the operator norm by the gradient norm.
  simpa [h₂, mul_assoc, mul_left_comm, mul_comm] using h₁
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
