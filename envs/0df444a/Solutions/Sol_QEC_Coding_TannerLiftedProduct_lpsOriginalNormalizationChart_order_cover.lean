-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizationChart_order_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:19:39.407329+00:00
-- url     : https://prove2.me/submissions/47604f04-847b-4a2f-bbaf-7e1d09e1ee7a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_additiveValuation_nonnegative_or_inverse


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
theorem _root_.solution (x : LPSOriginalFilledCurve N) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X) ∨
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹ :=
  additiveValuation_nonnegative_or_inverse (lpsOriginalFieldLocalOrder N hN hpos x) _
end QEC.Coding.TannerLiftedProduct
