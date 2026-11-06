-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.enorm_fderiv_apply_le_enorm_grad_mul
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:02:03.176098+00:00
-- url     : https://prove2.me/submissions/943e58de-b189-4c6d-a6c9-2b037baed26e

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

theorem solution (f : E → ℝ) (x a : E) :
    ‖fderiv ℝ f x a‖ₑ ≤ ‖grad (E := E) f x‖ₑ * ‖a‖ₑ := by
  have h : ‖fderiv ℝ f x a‖ ≤ ‖grad (E := E) f x‖ * ‖a‖ := by
    rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)]
    exact norm_inner_le_norm _ _
  simp only [enorm_eq_nnnorm, ← ENNReal.coe_mul]
  exact_mod_cast h
