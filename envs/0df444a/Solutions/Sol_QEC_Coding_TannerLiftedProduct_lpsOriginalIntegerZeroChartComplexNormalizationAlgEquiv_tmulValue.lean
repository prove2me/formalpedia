-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:56:43.56016+00:00
-- url     : https://prove2.me/submissions/53ee7e66-f6c6-47f1-b7ed-8401e8420e22

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureScalarExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexAffineNormalizationTensorAlgEquiv_tmulValue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerZeroNormalizationRationalTensorAlgEquiv_tmulValue
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
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary062
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary063
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary064
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary065
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary066
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary067
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary068
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary069
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary070
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary071
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary072
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary073
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary074
local notation "IZ" => integralClosure (Polynomial ℤ) FQ
local notation "IQ" => integralClosure (Polynomial ℚ) FQ
local notation "IC" => integralClosure (Polynomial ℂ) FC
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary075
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary076
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (c : ℂ) (x : lpsOriginalIntegerNormalZeroChart N hN) :
    (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN (c ⊗ₜ[ℤ] x)).val =
      algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN x.val := by
  unfold lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv
  dsimp only [id_eq]
  erw [AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  erw [lpsOriginalComplexAffineNormalizationTensorAlgEquiv_tmulValue]
  have hv := lpsOriginalIntegerZeroNormalizationRationalTensorAlgEquiv_tmulValue N hN (1 : ℚ) x
  erw [one_smul] at hv
  erw [hv]
  rfl
end QEC.Coding.TannerLiftedProduct
