-- Prove2me | solution 1 for StrictNestedSmoothJordanExhaustion.diffContOnCl_canonicalScalarCompanion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:47.77483+00:00
-- url     : https://prove2.me/submissions/159efc33-2773-48ea-a1a0-d1768f51a2ff

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Theorems.Thm_SmoothJordanDomain_canonicalNormal_support_all_of_support_at
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_exists_oriented_point_canonicalOrientation
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq
import Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
import Theorems.Thm_diffContOnCl_crouzeixPolynomialScalarCompanion_extension
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
namespace StrictNestedSmoothJordanExhaustion
theorem _root_.solution
    {K : Set ℂ} (Omega : StrictNestedSmoothJordanExhaustion K)
    (p : Polynomial ℂ) (n : ℕ) :
    DiffContOnCl ℂ
      (crouzeixPolynomialScalarCompanionClosedExtension
        (Omega.domain n).canonicalOrientation p)
      (Omega.domain n).canonicalOrientation.carrier := by
  let Psi := (Omega.domain n).canonicalOrientation
  obtain ⟨c, hc, hc0⟩ :=
    (Omega.domain n).exists_oriented_point_canonicalOrientation
  have hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Psi.boundaryParam t) *
        (c - Psi.boundaryParam t)).re ≤ 0 :=
    Psi.canonicalNormal_support_all_of_support_at c hc 0 hc0
  have hkernel : ∀ z ∈ Psi.carrier,
      crouzeixScalarCauchyKernel Psi z = 1 :=
    crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
      Psi c hc hcside
  have hbounded : Bornology.IsBounded Psi.carrier := by
    rw [show Psi.carrier = (Omega.domain n).carrier by
      exact SmoothJordanDomain.canonicalOrientation_carrier _]
    exact (Omega.isCompact_closure n).isBounded.subset subset_closure
  apply diffContOnCl_crouzeixPolynomialScalarCompanion_extension
    Psi p
      (crouzeixPolynomialScalarCompanionClosedExtension Psi p)
  · exact
      continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
        Psi p hbounded hkernel
  · intro z hz
    exact crouzeixPolynomialScalarCompanionClosedExtension_eq Psi p hz
end StrictNestedSmoothJordanExhaustion
