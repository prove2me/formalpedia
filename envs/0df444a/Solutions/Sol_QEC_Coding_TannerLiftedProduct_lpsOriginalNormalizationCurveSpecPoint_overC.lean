-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizationCurveSpecPoint_overC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:35:10.348604+00:00
-- url     : https://prove2.me/submissions/72c3b8f6-7649-4544-89f8-9142847a5079

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationOverlapEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationComplexPoints
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroNormalizationSpecPoint_overC
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityNormalizationSpecPoint_overC

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
theorem _root_.solution (x : LPSOriginalFilledCurve N) :
    lpsOriginalNormalizationCurveSpecPoint N hpos hN x ≫
      lpsOriginalComplexNormalGluedToSpecC N hpos = 𝟙 _ := by
  classical
  unfold lpsOriginalNormalizationCurveSpecPoint
  split_ifs with hj
  · rw [Category.assoc, lpsOriginalComplexNormalGluedToSpecC_chart]
    exact lpsOriginalZeroNormalizationSpecPoint_overC N hpos hN x hj
  · rw [Category.assoc, lpsOriginalComplexNormalGluedToSpecC_chart]
    exact lpsOriginalInfinityNormalizationSpecPoint_overC N hpos hN x _
end QEC.Coding.TannerLiftedProduct
