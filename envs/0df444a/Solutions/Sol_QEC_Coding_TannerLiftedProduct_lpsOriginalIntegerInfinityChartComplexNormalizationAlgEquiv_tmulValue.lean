-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:12:47.89741+00:00
-- url     : https://prove2.me/submissions/cb4491d8-9512-4d1c-bd71-8494c496d357

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexReciprocalNormalizationTensorAlgEquiv_tmulValue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerInfinityNormalizationRationalTensorAlgEquiv_tmulValue
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
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary041
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary042
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary043
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary044
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary045
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary046
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary047
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary048
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary049
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary050
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary051
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary052
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary053
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary054
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary055
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary056
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary057
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary058
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary059
local notation "IZ" => integralClosure (Polynomial ℤ) FQ
local notation "IQ" => integralClosure (Polynomial ℚ) FQ
local notation "IC" => integralClosure (Polynomial ℂ) FC
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary060
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary061
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (c : ℂ) (x : lpsOriginalIntegerNormalInfinityChart N hN) :
    (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN (c ⊗ₜ[ℤ] x)).val =
      algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN x.val := by
  unfold lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv
  dsimp only [id_eq]
  erw [AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  erw [lpsOriginalComplexReciprocalNormalizationTensorAlgEquiv_tmulValue]
  have hv := lpsOriginalIntegerInfinityNormalizationRationalTensorAlgEquiv_tmulValue N hN (1 : ℚ) x
  erw [one_smul] at hv
  erw [hv]
  rfl
end QEC.Coding.TannerLiftedProduct
