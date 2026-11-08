-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerInfinityNormalizationRationalTensorAlgEquiv_tmulValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:59:52.178196+00:00
-- url     : https://prove2.me/submissions/c933bb95-7803-47e0-8313-8220264bd394

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary030
variable (N : ℕ) (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "BP" => ℚ ⊗[ℤ] Polynomial ℤ
local notation "TB" => ℚ ⊗[ℤ] FQ
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary031
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary032
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary033
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary034
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary035
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary036
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary037
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary038
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary039
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary040
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q : ℚ) (x : integralClosure (Polynomial ℤ) FQ) :
    (lpsOriginalIntegerInfinityNormalizationRationalTensorAlgEquiv N hN (q ⊗ₜ[ℤ] x)).val =
      q • x.val := lpsOriginalIntegerInfinityNormalizationRationalTensorEquiv_tmulValue N hN q x
end QEC.Coding.TannerLiftedProduct
