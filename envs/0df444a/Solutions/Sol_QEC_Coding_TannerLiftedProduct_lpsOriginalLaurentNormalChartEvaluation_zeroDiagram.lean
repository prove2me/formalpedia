-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLaurentNormalChartEvaluation_zeroDiagram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:30:51.591788+00:00
-- url     : https://prove2.me/submissions/1d6f9914-fbd5-4c80-84e6-8a9e3492d5a6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationOverlapEvaluation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_9017904347_15
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_9017904347_16
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "ICL" => lpsOriginalComplexNormalLaurentChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_9017904347_22
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_9017904347_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_9017904347_24
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_9017904347_25
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    (lpsOriginalLaurentNormalChartEvaluation N hpos hN x hj hi).comp
      (lpsOriginalComplexNormalZeroToLaurent N hpos) =
        lpsOriginalZeroNormalChartEvaluation N hpos hN x hj := by
  apply RingHom.ext
  intro a
  rfl
end QEC.Coding.TannerLiftedProduct
