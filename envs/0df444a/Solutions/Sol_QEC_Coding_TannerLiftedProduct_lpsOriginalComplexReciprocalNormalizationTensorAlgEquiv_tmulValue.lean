-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexReciprocalNormalizationTensorAlgEquiv_tmulValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:59:26.433741+00:00
-- url     : https://prove2.me/submissions/f1cd85c9-9d6b-40c8-a15f-0ba96048d1f4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary001
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary012
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary016
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary018
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary023
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary024
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary025
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary026
local notation "BP" => ℂ ⊗[ℚ] Polynomial ℚ
local notation "TB" => ℂ ⊗[ℚ] FQ
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary027
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary028
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary029
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (c : ℂ) (x : integralClosure (Polynomial ℚ) FQ) :
    (lpsOriginalComplexReciprocalNormalizationTensorAlgEquiv N hN (c ⊗ₜ[ℚ] x)).val =
      algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN x.val :=
  lpsOriginalComplexReciprocalNormalizationTensorEquiv_tmulValue N hN c x
end QEC.Coding.TannerLiftedProduct
