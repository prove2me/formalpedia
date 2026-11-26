-- Prove2me | solution 1 for SmoothJordanDomain.hasSmoothJordanOuterApproximation_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:09:34.725201+00:00
-- url     : https://prove2.me/submissions/7153a06e-e62e-4f02-a506-8ec59162c2de

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanCompact
import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximation
import Definitions.Def_Operator_Crouzeix_SmoothJordanInflation
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_exists_pos_radius_closure_subset_ball
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_deriv
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_outwardNormal
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_closure_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_frontier_carrier
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_deriv
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_outwardNormal
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_closure_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_frontier_carrier
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Metric Set
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    HasSmoothJordanOuterApproximation (closure Omega.carrier) := by
  intro ε hε
  obtain ⟨c, hc⟩ := Omega.carrier_nonempty
  obtain ⟨R, hR, hclosedBall⟩ :=
    Omega.exists_pos_radius_closure_subset_ball c
  let s : ℝ := ε / (2 * R)
  have hs : 0 < s := by
    dsimp only [s]
    exact div_pos hε (mul_pos (by norm_num) hR)
  let t : ℝ := 1 + s
  have ht : 1 < t := by
    dsimp only [t]
    linarith
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have htC : (t : ℂ) ≠ 0 := by
    exact_mod_cast ht0
  let b : ℂ := (1 - (t : ℂ)) * c
  let Psi := Omega.complexAffine (t : ℂ) b htC
  have hhomothety (z : ℂ) :
      (t : ℂ) * z + b = AffineMap.homothety c t z := by
    dsimp only [b]
    rw [AffineMap.homothety_apply]
    change (t : ℂ) * z + (1 - (t : ℂ)) * c =
      (t : ℂ) * (z - c) + c
    ring
  have hcInterior : c ∈ interior Omega.carrier := by
    rw [Omega.isOpen_carrier.interior_eq]
    exact hc
  have hinside : closure Omega.carrier ⊆ Psi.carrier := by
    have hconvex := Omega.strictConvex_carrier.convex
    have hhom :=
      hconvex.closure_subset_image_homothety_interior_of_one_lt
        hcInterior t ht
    change closure Omega.carrier ⊆
      (fun z => (t : ℂ) * z + b) '' Omega.carrier
    rw [show (fun z : ℂ => (t : ℂ) * z + b) =
        AffineMap.homothety c t by
      funext z
      exact hhomothety z]
    simpa only [Omega.isOpen_carrier.interior_eq] using hhom
  refine ⟨Psi, hinside, ?_⟩
  have hclosure : closure Psi.carrier =
      (fun z => (t : ℂ) * z + b) '' closure Omega.carrier := by
    let e : ℂ ≃ₜ ℂ :=
      (Homeomorph.mulLeft₀ (t : ℂ) htC).trans (Homeomorph.addRight b)
    change closure (e '' Omega.carrier) = e '' closure Omega.carrier
    exact (e.image_closure Omega.carrier).symm
  rw [hclosure]
  rintro y ⟨z, hz, rfl⟩
  apply Metric.mem_thickening_iff.mpr
  refine ⟨z, hz, ?_⟩
  change dist ((t : ℂ) * z + b) z < ε
  rw [hhomothety, dist_homothety_self]
  have hnorm : ‖1 - t‖ = s := by
    have hsub : 1 - t = -s := by
      dsimp only [t]
      ring
    rw [hsub, Real.norm_eq_abs, abs_neg, abs_of_pos hs]
  rw [hnorm]
  have hzR : dist c z < R := by
    rw [dist_comm]
    exact hclosedBall hz
  have hsR : s * R = ε / 2 := by
    dsimp only [s]
    field_simp [hR.ne']
  calc
    s * dist c z < s * R := mul_lt_mul_of_pos_left hzR hs
    _ = ε / 2 := hsR
    _ < ε := half_lt_self hε
end SmoothJordanDomain
