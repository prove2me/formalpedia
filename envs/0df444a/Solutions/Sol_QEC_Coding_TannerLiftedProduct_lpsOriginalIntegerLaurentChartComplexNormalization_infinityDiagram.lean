-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerLaurentChartComplexNormalization_infinityDiagram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:41:23.827223+00:00
-- url     : https://prove2.me/submissions/f04efe81-3fde-4306-be90-4baaec14edcc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
import Mathlib.RingTheory.Localization.BaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLaurentNormalizationComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerLaurentChartComplexNormalization_tmulValue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue


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
theorem _root_.solution
    (c : ℂ) (a : lpsOriginalIntegerNormalInfinityChart N hN) :
    lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv N hN
      (c ⊗ₜ[ℤ] lpsOriginalIntegerNormalInfinityToLaurent N hN a) =
      lpsOriginalComplexNormalInfinityToLaurent N hN
        (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN (c ⊗ₜ[ℤ] a)) := by
  apply Subtype.ext
  change (lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv N hN
      (c ⊗ₜ[ℤ] lpsOriginalIntegerNormalInfinityToLaurent N hN a)).val =
    (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN (c ⊗ₜ[ℤ] a)).val
  exact (lpsOriginalIntegerLaurentChartComplexNormalization_tmulValue N hN c
    (lpsOriginalIntegerNormalInfinityToLaurent N hN a)).trans
    (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue N hN c a).symm
end QEC.Coding.TannerLiftedProduct
