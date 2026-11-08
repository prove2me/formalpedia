-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:04:41.788892+00:00
-- url     : https://prove2.me/submissions/dad2f707-08d1-4c69-8788-c2c95e477c74

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationComplexPoints
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroMeromorphicValuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityMeromorphicValuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationChart_order_cover


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_22
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_27
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_28
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_29
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_30
local notation "IC0" => lpsOriginalComplexNormalZeroChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_59
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_60
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_112
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_113
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x : LPSOriginalFilledCurve N) :
    IsDiscreteValuationRing
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring := by
  rcases lpsOriginalNormalizationChart_order_cover N hpos hN x with hj | hi
  · exact lpsOriginalZeroMeromorphicValuationRing_isDiscreteValuationRing N hpos hN x hj
  · exact lpsOriginalInfinityMeromorphicValuationRing_isDiscreteValuationRing N hpos hN x hi
end QEC.Coding.TannerLiftedProduct
