-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalZeroNormalChartEvaluation_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:23:14.400447+00:00
-- url     : https://prove2.me/submissions/26086bbd-5b59-4720-9fd9-be0f17aba645

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroConstantChart_value
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_meromorphicNoPoleEvaluation_rep
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_constant


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_18
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_19
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "IC0" => lpsOriginalComplexNormalZeroChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_26
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_27
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_28
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_30
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_31
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) (c : ℂ) :
    lpsOriginalZeroNormalChartEvaluation N hpos hN x hj
      (lpsOriginalComplexZeroConstantRingHom N hpos c) = c := by
  apply meromorphicNoPoleEvaluation_rep _ _ (fun _ => c) analyticAt_const
  change (lpsOriginalFieldToLocal N hN hpos x
    (lpsOriginalComplexZeroConstantRingHom N hpos c).val).val =
      ((fun _ : ℂ => c) : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ)
  rw [lpsOriginalZeroConstantChart_value, lpsOriginalFieldToLocal_constant]
  rfl
end QEC.Coding.TannerLiftedProduct
