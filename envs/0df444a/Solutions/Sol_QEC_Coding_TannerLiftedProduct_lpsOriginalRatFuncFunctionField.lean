-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncFunctionField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:35:14.131234+00:00
-- url     : https://prove2.me/submissions/daf0782e-0625-4d92-8d41-c1825a14b413

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finiteDimensional


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
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : _root_.FunctionField ℂ K := by
  let : FiniteDimensional J K := lpsOriginalGeneratedFunctionField_finiteDimensional N hpos
  apply Module.Finite.of_equiv_equiv (A₁ := J) (B₁ := K)
    lpsOriginalRatFuncToJ.symm.toRingEquiv (RingEquiv.refl K)
  apply RingHom.ext
  intro x
  change algebraMap J K (lpsOriginalRatFuncToJ (lpsOriginalRatFuncToJ.symm x)) =
    algebraMap J K x
  rw [AlgEquiv.apply_symm_apply]
end QEC.Coding.TannerLiftedProduct
