-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerBase_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:19:28.217464+00:00
-- url     : https://prove2.me/submissions/1c5ced3f-ce7c-4b51-bc2c-84f12cd53fdc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerBaseFractionMap_injective
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
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    letI := lpsOriginalIntegerBaseFractionMap.toAlgebra
    IsFractionRing (Polynomial ℤ) (FractionRing (Polynomial ℚ)) := by
  let := lpsOriginalIntegerBaseFractionMap.toAlgebra
  let : FaithfulSMul (Polynomial ℤ) (FractionRing (Polynomial ℚ)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      lpsOriginalIntegerBaseFractionMap_injective
  apply IsFractionRing.of_field
  intro x
  obtain ⟨p,q,hq,rfl⟩ := IsFractionRing.div_surjective (Polynomial ℚ) x
  obtain ⟨m,hm,hp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  obtain ⟨n,hn,hq'⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) q
  let P := IsLocalization.integerNormalization (nonZeroDivisors ℤ) p
  let Q := IsLocalization.integerNormalization (nonZeroDivisors ℤ) q
  have hP : lpsOriginalIntegerBaseFractionMap P=
      (m:FractionRing (Polynomial ℚ))*algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) p := by
    simpa only [lpsOriginalIntegerBaseFractionMap,RingHom.comp_apply,
      Polynomial.coe_mapRingHom,zsmul_eq_mul,map_mul,map_intCast] using
        congrArg (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))) hp
  have hQ : lpsOriginalIntegerBaseFractionMap Q=
      (n:FractionRing (Polynomial ℚ))*algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) q := by
    simpa only [lpsOriginalIntegerBaseFractionMap,RingHom.comp_apply,
      Polynomial.coe_mapRingHom,zsmul_eq_mul,map_mul,map_intCast] using
        congrArg (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))) hq'
  have hC (a : ℤ) : lpsOriginalIntegerBaseFractionMap (Polynomial.C a)=
      (a:FractionRing (Polynomial ℚ)) := by
    simp [lpsOriginalIntegerBaseFractionMap]
  have hm' : (m:FractionRing (Polynomial ℚ))≠0 :=
    Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hm)
  have hn' : (n:FractionRing (Polynomial ℚ))≠0 :=
    Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hn)
  have hqF : algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) q≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ)))).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hq)
  refine ⟨P*Polynomial.C n,Q*Polynomial.C m,?_⟩
  change algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) p /
      algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) q=
    lpsOriginalIntegerBaseFractionMap (P*Polynomial.C n) /
      lpsOriginalIntegerBaseFractionMap (Q*Polynomial.C m)
  rw [map_mul,map_mul,hP,hQ,hC,hC]
  field_simp [hm',hn',hqF]
end QEC.Coding.TannerLiftedProduct
