-- Prove2me | solution 1 for canonicalNormal_support_all_of_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:21.312458+00:00
-- url     : https://prove2.me/submissions/70430ab2-2edf-4b33-80b7-1ad6107764d1

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


section
open Complex Filter MeasureTheory Set
open scoped Interval Real
private theorem periodic_deriv_boundaryParam (Omega : SmoothJordanDomain) :
    Function.Periodic (deriv Omega.boundaryParam) (2 * Real.pi) := by
  intro t
  have hfun : (fun x : ℝ => Omega.boundaryParam (x + 2 * Real.pi)) =
      Omega.boundaryParam := by
    funext x
    exact Omega.boundaryParam_periodic x
  have h := congrArg (fun f : ℝ → ℂ => deriv f t) hfun
  rwa [deriv_comp_add_const] at h
end

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (c : ℂ)
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0 := by
  let f : ℝ → ℝ := fun t =>
    ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
      (c - Omega.boundaryParam t)).re
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro t
    dsimp only [f]
    rw [periodic_deriv_boundaryParam Omega t,
      Omega.boundaryParam_periodic t]
  intro t
  obtain ⟨u, hu, htu⟩ :=
    hf.exists_mem_Ioc Real.two_pi_pos t 0
  change f t ≤ 0
  rw [htu]
  exact hsupport u (by simpa only [zero_add] using hu)
