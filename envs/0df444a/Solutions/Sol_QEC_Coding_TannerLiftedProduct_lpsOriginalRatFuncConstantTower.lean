-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncConstantTower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:35:57.751306+00:00
-- url     : https://prove2.me/submissions/cc0ef4a0-1a11-4942-a550-388cb631d910

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison

set_option autoImplicit false
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
noncomputable section
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
variable (N : ℕ) (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_3d79f03ea9_67
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_3d79f03ea9_70
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_3d79f03ea9_71
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_3d79f03ea9_72
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_3d79f03ea9_73
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_3d79f03ea9_77
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : IsScalarTower ℂ (RatFunc ℂ) K := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap J K (algebraMap ℂ J c) =
    algebraMap J K (lpsOriginalRatFuncToJ (algebraMap ℂ (RatFunc ℂ) c))
  rw [AlgEquiv.commutes]
end QEC.Coding.TannerLiftedProduct
