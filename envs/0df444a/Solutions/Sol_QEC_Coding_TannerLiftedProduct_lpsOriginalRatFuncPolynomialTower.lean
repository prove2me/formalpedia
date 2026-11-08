-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncPolynomialTower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:41:04.338848+00:00
-- url     : https://prove2.me/submissions/df76376c-79d9-4344-ae3e-7d26bdf6fb4c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncToJ_polynomial

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
theorem _root_.solution : IsScalarTower P (RatFunc ℂ) K := by
  apply IsScalarTower.of_algebraMap_eq
  intro p
  change algebraMap J K (algebraMap P J p) =
    algebraMap J K (lpsOriginalRatFuncToJ (algebraMap P (RatFunc ℂ) p))
  rw [lpsOriginalRatFuncToJ_polynomial]
end QEC.Coding.TannerLiftedProduct
