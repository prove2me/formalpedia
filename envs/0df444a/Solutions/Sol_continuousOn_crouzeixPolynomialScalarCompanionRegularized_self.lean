-- Prove2me | solution 1 for continuousOn_crouzeixPolynomialScalarCompanionRegularized_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:22.629934+00:00
-- url     : https://prove2.me/submissions/9ca88056-7dde-4dff-936e-e5ece0f30228

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_continuous_eval_divByMonic_X_sub_C
import Theorems.Thm_exists_uniform_norm_eval_divByMonic_X_sub_C_frontier_le
import Theorems.Thm_ae_boundaryParam_ne_of_mem_frontier
import Theorems.Thm_contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ContinuousOn
      (fun xi =>
        crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)
      (frontier Omega.carrier) := by
  intro xi hxi
  let l : Filter ℂ := nhdsWithin xi (frontier Omega.carrier)
  let q : ℂ → Polynomial ℂ := fun eta =>
    p /ₘ (Polynomial.X - Polynomial.C eta)
  let H : ℂ → ℝ → ℂ := fun eta t =>
    deriv Omega.boundaryParam t •
      (star (Omega.boundaryParam t - eta) *
        star (Polynomial.eval (Omega.boundaryParam t) (q eta)) *
          (Omega.boundaryParam t - eta)⁻¹)
  obtain ⟨Q, hQ, hq⟩ :=
    exists_uniform_norm_eval_divByMonic_X_sub_C_frontier_le Omega p
  let bound : ℝ → ℝ := fun t => Q * ‖deriv Omega.boundaryParam t‖
  have hboundCont : Continuous bound :=
    continuous_const.mul
      (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).norm
  have hboundInt : IntervalIntegrable bound MeasureTheory.volume
      (0 : ℝ) (2 * Real.pi) := hboundCont.intervalIntegrable _ _
  have hHmeas : ∀ᶠ eta in l,
      AEStronglyMeasurable (H eta)
        (MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [self_mem_nhdsWithin] with eta heta
    have hint :=
      contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
        Omega eta (q eta)
    change IntervalIntegrable
        (fun t : ℝ => deriv Omega.boundaryParam t •
          (star (Omega.boundaryParam t - eta) *
            star (Polynomial.eval (Omega.boundaryParam t) (q eta)) *
              (Omega.boundaryParam t - eta)⁻¹))
        MeasureTheory.volume (0 : ℝ) (2 * Real.pi) at hint
    exact hint.def'.aestronglyMeasurable
  have hHbound : ∀ᶠ eta in l,
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
        ‖H eta t‖ ≤ bound t := by
    filter_upwards [self_mem_nhdsWithin] with eta heta
    filter_upwards with t
    intro _ht
    have hsigma : Omega.boundaryParam t ∈ frontier Omega.carrier := by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self t
    let d := Omega.boundaryParam t - eta
    by_cases hd : d = 0
    · simp only [H, d] at hd ⊢
      rw [hd]
      simp only [star_zero, zero_mul, inv_zero, mul_zero, smul_zero,
        norm_zero]
      exact mul_nonneg hQ (norm_nonneg _)
    · have hdNorm : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
      have hqbound := hq eta heta (Omega.boundaryParam t) hsigma
      simp only [H, smul_eq_mul, norm_mul, norm_star, norm_inv]
      change ‖deriv Omega.boundaryParam t‖ *
          (‖d‖ * ‖Polynomial.eval (Omega.boundaryParam t) (q eta)‖ * ‖d‖⁻¹) ≤
        Q * ‖deriv Omega.boundaryParam t‖
      have hcancel :
          ‖d‖ * ‖Polynomial.eval (Omega.boundaryParam t) (q eta)‖ * ‖d‖⁻¹ =
            ‖Polynomial.eval (Omega.boundaryParam t) (q eta)‖ := by
        field_simp
      rw [hcancel]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hqbound
          (norm_nonneg (deriv Omega.boundaryParam t))
  have hHlim : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Ι (0 : ℝ) (2 * Real.pi) →
        Filter.Tendsto (fun eta => H eta t) l (nhds (H xi t)) := by
    filter_upwards [ae_boundaryParam_ne_of_mem_frontier Omega hxi] with t htne
    intro ht
    let sigma := Omega.boundaryParam t
    have hsigma : sigma ≠ xi := htne ht
    have hqcont : Continuous (fun eta : ℂ =>
        Polynomial.eval sigma (q eta)) := by
      exact (continuous_eval_divByMonic_X_sub_C p).comp
        (continuous_id.prodMk continuous_const)
    have hden : ContinuousAt (fun eta : ℂ => sigma - eta) xi := by
      fun_prop
    have hden0 : sigma - xi ≠ 0 := sub_ne_zero.mpr hsigma
    have hcont : ContinuousAt (fun eta => H eta t) xi := by
      change ContinuousAt (fun eta : ℂ =>
        deriv Omega.boundaryParam t •
          (star (sigma - eta) * star (Polynomial.eval sigma (q eta)) *
            (sigma - eta)⁻¹)) xi
      have hderiv : ContinuousAt
          (fun _ : ℂ => deriv Omega.boundaryParam t) xi := continuousAt_const
      exact hderiv.smul
        ((hden.star.mul hqcont.continuousAt.star).mul (hden.inv₀ hden0))
    have hl : l ≤ nhds xi := by
      dsimp only [l, nhdsWithin]
      exact inf_le_left
    exact hcont.tendsto.mono_left hl
  have hIntegral : Filter.Tendsto
      (fun eta => ∫ t in (0 : ℝ)..(2 * Real.pi), H eta t)
      l (nhds (∫ t in (0 : ℝ)..(2 * Real.pi), H xi t)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      bound hHmeas hHbound hboundInt hHlim
  have hscaled : Filter.Tendsto
      (fun eta => (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in (0 : ℝ)..(2 * Real.pi), H eta t)
      l (nhds ((2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in (0 : ℝ)..(2 * Real.pi), H xi t)) :=
    tendsto_const_nhds.mul hIntegral
  change Filter.Tendsto
    (fun eta =>
      crouzeixPolynomialScalarCompanionRegularized Omega p eta eta)
    l (nhds
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi))
  simpa only [l, q, H,
    crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic,
    contourIntegral] using hscaled
