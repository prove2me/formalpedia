-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFractionFieldEquiv_fieldPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:12:35.527182+00:00
-- url     : https://prove2.me/submissions/d3781241-1778-4165-9533-4d71207e9022

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (R : CommRingCat.{u}) [IsDomain R]
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F] :
    Spec.map (CommRingCat.ofHom (IsFractionRing.ringEquivOfRingEquiv
      (K := (Spec R).functionField) (L := F) (RingEquiv.refl R)).toRingHom) ≫
        (Spec R).fromSpecStalk (genericPoint (Spec R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
  rw [Spec.fromSpecStalk_eq', ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change IsFractionRing.ringEquivOfRingEquiv
    (K := (Spec R).functionField) (L := F) (RingEquiv.refl R)
      (algebraMap R (Spec R).functionField r) = algebraMap R F r
  simpa only [RingEquiv.refl_apply] using
    IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (K := (Spec R).functionField) (L := F) (RingEquiv.refl R) r
end QEC.Coding.TannerLiftedProduct
