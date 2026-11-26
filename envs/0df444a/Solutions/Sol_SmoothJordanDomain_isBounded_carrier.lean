-- Prove2me | solution 1 for SmoothJordanDomain.isBounded_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:05:14.100069+00:00
-- url     : https://prove2.me/submissions/d546867d-407a-4efc-8902-38981229a57e

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_SmoothJordanCompact
import Theorems.Thm_SmoothJordanDomain_canonicalNormal_support_all_of_support_at
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_exists_oriented_point_canonicalOrientation
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
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



set_option autoImplicit false
open Complex Metric Set
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    Bornology.IsBounded Omega.carrier := by
  let Psi := Omega.canonicalOrientation
  obtain ⟨c, hc, hc0⟩ := Omega.exists_oriented_point_canonicalOrientation
  have hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Psi.boundaryParam t) *
        (c - Psi.boundaryParam t)).re ≤ 0 :=
    Psi.canonicalNormal_support_all_of_support_at c hc 0 hc0
  have hkernel : ∀ z ∈ Psi.carrier,
      crouzeixScalarCauchyKernel Psi z = 1 :=
    crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
      Psi c hc hcside
  have hbounded : Bornology.IsBounded Psi.carrier :=
    Psi.isBounded_carrier_of_cauchyKernel_eq_one hkernel
  simpa only [Psi, SmoothJordanDomain.canonicalOrientation_carrier] using hbounded
end SmoothJordanDomain
