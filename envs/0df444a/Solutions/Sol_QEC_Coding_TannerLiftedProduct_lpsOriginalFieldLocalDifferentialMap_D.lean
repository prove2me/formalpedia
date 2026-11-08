-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLocalDifferentialMap_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:16:15.045839+00:00
-- url     : https://prove2.me/submissions/fb51ff4e-8451-48f4-ae7f-d19fa89cfafe

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_fieldLocalDifferentialMap_D


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_25
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_30
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_31
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_32
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_33
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_34
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_38
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_40
variable (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_47
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_58
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_59
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_60
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_61
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_62
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_63
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_64
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_68
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_70
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_72
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_75
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_dde5696b56_78
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f : K) :
    lpsOriginalFieldLocalDifferentialMap N hpos hN x (KaehlerDifferential.D ℂ K f) =
      germDerivative a (lpsOriginalFieldToLocal N hN hpos x f) :=
  QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.fieldLocalDifferentialMap_D K a f
end QEC.Coding.TannerLiftedProduct
