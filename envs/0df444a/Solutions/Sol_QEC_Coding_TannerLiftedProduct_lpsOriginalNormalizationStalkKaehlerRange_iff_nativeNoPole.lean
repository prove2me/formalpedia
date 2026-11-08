-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizationStalkKaehlerRange_iff_nativeNoPole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:46:47.651927+00:00
-- url     : https://prove2.me/submissions/0b22d284-e66d-4e60-8247-9a3f0eaaeb18

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_StalkScalars
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationStalkDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationStalkKaehlerRange_iff_valuation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLocalKaehlerRange_iff_nativeNoPole


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
      0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
        (lpsOriginalNativeCovectorToLocal N hN x
          (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm)) := by
  rw [lpsOriginalNormalizationStalkKaehlerRange_iff_valuation]
  change differentialForm ∈
    ((KaehlerDifferential.D ℂ K).compAlgebraMap V).liftKaehlerDifferential.range ↔ _
  exact lpsOriginalLocalKaehlerRange_iff_nativeNoPole
    (N := N) (hN := hN) (x := x) (hpos := hpos) differentialForm
end QEC.Coding.TannerLiftedProduct
