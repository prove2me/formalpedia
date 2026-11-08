-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizationStalkKaehlerRange_iff_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:56:40.943481+00:00
-- url     : https://prove2.me/submissions/62568929-1946-40c2-b26d-8adbbae9c92a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_StalkScalars
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationStalkDifferentialComparison
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_range_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped TensorProduct
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_29
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "IC0" => lpsOriginalComplexNormalZeroChart N hpos
local notation "ICI" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_36
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_37
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_38
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_39
variable (x : LPSOriginalFilledCurve N)
local notation "St" => lpsOriginalNormalizationPointStalk N hpos hN x
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_192
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_193
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_214
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_215
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_217
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_218
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_220
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_221
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_223
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_225
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_229
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_234
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_239
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_243
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_245
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_247
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_249
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_251
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_253
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_255
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_777eb8c026_257
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (differentialForm : KaehlerDifferential ℂ K) :
    differentialForm ∈ (KaehlerDifferential.map ℂ ℂ St K).range ↔
      differentialForm ∈ (KaehlerDifferential.map ℂ ℂ V K).range := by
  apply kaehler_field_map_range_iff ℂ St V K
  exact (lpsOriginalNormalizationStalkValuationComplexAlgEquiv N hpos hN x).surjective
end QEC.Coding.TannerLiftedProduct
