-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInversePolynomialMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:51:05.024146+00:00
-- url     : https://prove2.me/submissions/b3485f2f-ca7f-4e9e-a653-0c4dc012f8ca

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncToJ_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncToJ_involution

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
variable [NeZero N]
omit [NeZero N]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    InverseAffinePlace.transportedPolynomialMap (k := ℂ) (F := K)
      (oldRationalAlgebra := lpsOriginalRatFuncAlgebra N hpos) =
      lpsOriginalReciprocalComplexFieldPolynomialMap N hpos := by
  apply RingHom.ext
  intro p
  change algebraMap J K
      (lpsOriginalRatFuncToJ
        (InverseAffinePlace.rationalInvolution ℂ (algebraMap P (RatFunc ℂ) p))) =
    algebraMap J K (lpsOriginalComplexJFractionInversion (algebraMap P J p))
  rw [lpsOriginalRatFuncToJ_involution, lpsOriginalRatFuncToJ_polynomial]
end QEC.Coding.TannerLiftedProduct
