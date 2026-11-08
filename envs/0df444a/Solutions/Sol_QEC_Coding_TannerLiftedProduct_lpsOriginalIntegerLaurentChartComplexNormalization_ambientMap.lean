-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerLaurentChartComplexNormalization_ambientMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:26:27.501763+00:00
-- url     : https://prove2.me/submissions/fc0a212d-76e1-45bc-8ca1-c94439ee2d09

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
import Mathlib.RingTheory.Localization.BaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLaurentNormalizationComparison
import Theorems.Thm_QEC_Coding_OriginalNormalizationComparison_ChartLocalization_tensorRingHom_ext_tmul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerLaurentChartComplexNormalization_algebraMap
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalZeroToLaurent_algebraMapValue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerLaurentConstantTensorMap_zeroRingHomValue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue
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
local notation "JC" => FractionRing (Polynomial ℂ)
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary001
variable (N : ℕ) (hN : 0 < N)
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary008
local notation "IC0" => integralClosure (Polynomial ℂ) FC
local notation "ICL" => integralClosure (LaurentPolynomial ℂ) FC
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary016
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary018
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary023
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary024
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary025
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary026
local notation "IZ" => lpsOriginalIntegerNormalZeroChart N hN
local notation "IL" => lpsOriginalIntegerNormalLaurentChart N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary027
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary028
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary029
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary030
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary031
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary032
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary033
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary034
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary035
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary036
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary037
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary038
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary039
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary040
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary041
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary042
variable [NeZero N]
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary043
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary044
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary045
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary046
local notation "TIZ" => ℂ ⊗[ℤ] IZ
local notation "TIL" => ℂ ⊗[ℤ] IL
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary047
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary048
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary049
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary050
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary051
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary052
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    (integralClosure (LaurentPolynomial ℂ) FC).val.toRingHom.comp
      (lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv N hN).toRingHom =
      (lpsOriginalIntegerLaurentConstantTensorMap N hN).toRingHom := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers ((1 : ℂ) ⊗ₜ[ℤ] algebraMap (Polynomial ℤ) IZ Polynomial.X))
  apply QEC.Coding.OriginalNormalizationComparison.ChartLocalization.tensorRingHom_ext_tmul (R := ℤ) (S := ℂ) (A := IZ)
  intro c a
  dsimp only [RingHom.comp_apply]
  erw [lpsOriginalIntegerLaurentChartComplexNormalization_algebraMap]
  have ht : algebraMap TIZ TIL (c ⊗ₜ[ℤ] a) =
      c ⊗ₜ[ℤ] lpsOriginalIntegerNormalZeroToLaurent N hN a := by
    change Algebra.TensorProduct.map (AlgHom.id ℂ ℂ)
      (lpsOriginalIntegerNormalZeroToLaurent N hN).toIntAlgHom (c ⊗ₜ[ℤ] a) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  rw [ht]
  exact (lpsOriginalComplexNormalZeroToLaurent_algebraMapValue N hN
    (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN (c ⊗ₜ[ℤ] a))).trans
    ((lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue N hN c a).trans
      (lpsOriginalIntegerLaurentConstantTensorMap_zeroRingHomValue N hN c a).symm)
end QEC.Coding.TannerLiftedProduct
