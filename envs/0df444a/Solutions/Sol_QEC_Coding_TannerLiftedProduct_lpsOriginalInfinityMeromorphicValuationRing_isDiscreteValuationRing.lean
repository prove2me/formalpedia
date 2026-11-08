-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityMeromorphicValuationRing_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:12:34.755522+00:00
-- url     : https://prove2.me/submissions/3a91b95e-010a-4984-a018-1a91dc278b77

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationComplexPoints
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ValuationCentres_heightOneValuationRing_isDiscreteValuationRing


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
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_206
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_207
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_208
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_209
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_210
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_211
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_212
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_213
local notation "ICI" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_272
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_273
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (((algebraMap J K).comp lpsOriginalCanonicalComplexPolynomialFractionMap) Polynomial.X)⁻¹) :
    IsDiscreteValuationRing
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring := by
  let H := lpsOriginalInfinityHeightOneCentre N hpos hN x h
  let : IsDiscreteValuationRing (H.valuationSubringAtPrime K) :=
    heightOneValuationRing_isDiscreteValuationRing ICI H
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring (lpsOriginalInfinityHeightOneCentre_valuationRing N hpos hN x h)))
end QEC.Coding.TannerLiftedProduct
