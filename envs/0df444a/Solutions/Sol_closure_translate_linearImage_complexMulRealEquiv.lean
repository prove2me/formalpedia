-- Prove2me | solution 1 for closure_translate_linearImage_complexMulRealEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:05:45.319252+00:00
-- url     : https://prove2.me/submissions/2c799c4f-7e1a-4b51-9a79-6f8bb4073809

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity
import Theorems.Thm_complexMulRealEquiv_apply
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_ellipse_boundaryParam
import Theorems.Thm_SmoothJordanDomain_ellipse_boundaryParam_deriv
import Theorems.Thm_SmoothJordanDomain_ellipse_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_translate_boundaryParam
import Theorems.Thm_SmoothJordanDomain_translate_boundaryParam_apply
import Theorems.Thm_SmoothJordanDomain_translate_boundaryParam_deriv
import Theorems.Thm_SmoothJordanDomain_translate_carrier
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
attribute [local simp] SmoothJordanDomain.ellipse_boundaryParam
attribute [local simp] SmoothJordanDomain.ellipse_boundaryParam_deriv
attribute [local simp] SmoothJordanDomain.ellipse_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] SmoothJordanDomain.translate_boundaryParam
attribute [local simp] SmoothJordanDomain.translate_boundaryParam_apply
attribute [local simp] SmoothJordanDomain.translate_boundaryParam_deriv
attribute [local simp] SmoothJordanDomain.translate_carrier
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


attribute [local simp] complexMulRealEquiv_apply

set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
theorem _root_.solution
    (Omega : SmoothJordanDomain) (c a : ℂ) (ha : a ≠ 0) :
    closure
        (((Omega.linearImage (complexMulRealEquiv a ha)).translate c).carrier) =
      (fun z => c + a * z) '' closure Omega.carrier := by
  change closure ((fun z => c + z) ''
      (complexMulRealEquiv a ha '' Omega.carrier)) =
    (fun z => c + a * z) '' closure Omega.carrier
  have hadd :=
    ((Homeomorph.addLeft c).image_closure
      (complexMulRealEquiv a ha '' Omega.carrier)).symm
  change closure ((fun z => c + z) ''
      (complexMulRealEquiv a ha '' Omega.carrier)) =
    (fun z => c + z) '' closure
      (complexMulRealEquiv a ha '' Omega.carrier) at hadd
  rw [hadd]
  have hlinear :=
    ((complexMulRealEquiv a ha).toHomeomorph.image_closure
      Omega.carrier).symm
  change closure (complexMulRealEquiv a ha '' Omega.carrier) =
    complexMulRealEquiv a ha '' closure Omega.carrier at hlinear
  rw [hlinear]
  ext z
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨a * w, ⟨w, hw, rfl⟩, rfl⟩
