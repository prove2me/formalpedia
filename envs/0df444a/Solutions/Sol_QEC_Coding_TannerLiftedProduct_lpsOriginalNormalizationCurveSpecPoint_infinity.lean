-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizationCurveSpecPoint_infinity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:42:43.822263+00:00
-- url     : https://prove2.me/submissions/e4bc8415-0f52-412d-bc1e-150ce04ed5d1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationOverlapEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationComplexPoints
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationSpecPoint_gluedAgreement

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_18
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_19
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_24
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_25
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_26
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_27
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    lpsOriginalNormalizationCurveSpecPoint N hpos hN x =
      lpsOriginalInfinityNormalizationSpecPoint N hpos hN x hi ≫
        lpsOriginalComplexNormalGluedChartMap N hpos true := by
  classical
  unfold lpsOriginalNormalizationCurveSpecPoint
  split_ifs with hj
  · exact lpsOriginalNormalizationSpecPoint_gluedAgreement N hpos hN x hj hi
  · rfl
end QEC.Coding.TannerLiftedProduct
