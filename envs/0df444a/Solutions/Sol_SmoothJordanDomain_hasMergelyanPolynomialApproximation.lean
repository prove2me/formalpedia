-- Prove2me | solution 1 for SmoothJordanDomain.hasMergelyanPolynomialApproximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:20:15.9374+00:00
-- url     : https://prove2.me/submissions/f3bfa539-d11c-4fea-93ce-33691ee54d64

import Definitions.Def_Operator_Crouzeix_ConvexRungeIntegral
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
import Theorems.Thm_SmoothJordanDomain_hasMergelyanPolynomialApproximation_of_cauchyFormula
import Theorems.Thm_SmoothJordanDomain_canonicalNormal_support_all_of_support_at
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_exists_oriented_point_canonicalOrientation
import Theorems.Thm_SmoothJordanDomain_isCompact_closure_of_cauchyKernel_eq_one
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_deriv
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_outwardNormal
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_closure_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_frontier_carrier
import Theorems.Thm_cauchyFormula_canonicalOrientation
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
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
open Complex Filter Metric Set
open scoped Interval Real Topology
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    Omega.HasMergelyanPolynomialApproximation := by
  let Psi := Omega.canonicalOrientation
  have hPsi : Psi.HasMergelyanPolynomialApproximation := by
    obtain ⟨c, hc, hc0⟩ := Omega.exists_oriented_point_canonicalOrientation
    have hcside : ∀ t : ℝ,
        ((starRingEnd ℂ) (-I * deriv Psi.boundaryParam t) *
          (c - Psi.boundaryParam t)).re ≤ 0 :=
      Psi.canonicalNormal_support_all_of_support_at c hc 0 hc0
    have hkernel : ∀ z ∈ Psi.carrier,
        crouzeixScalarCauchyKernel Psi z = 1 :=
      crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
        Psi c hc hcside
    have hcompact : IsCompact (closure Psi.carrier) :=
      Psi.isCompact_closure_of_cauchyKernel_eq_one hkernel
    apply Psi.hasMergelyanPolynomialApproximation_of_cauchyFormula hcompact
    intro f hf z hz
    have hfOmega : DiffContOnCl ℂ f Omega.carrier := by
      simpa only [Psi, SmoothJordanDomain.canonicalOrientation_carrier] using hf
    have hzOmega : z ∈ Omega.carrier := by
      simpa only [Psi, SmoothJordanDomain.canonicalOrientation_carrier] using hz
    change f z = (2 * (Real.pi : ℂ) * I)⁻¹ *
      contourIntegral (fun xi => f xi * (xi - z)⁻¹) Psi.boundaryParam
    exact cauchyFormula_canonicalOrientation Omega hfOmega hzOmega
  exact
    (SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
      Omega).mp hPsi
end SmoothJordanDomain
