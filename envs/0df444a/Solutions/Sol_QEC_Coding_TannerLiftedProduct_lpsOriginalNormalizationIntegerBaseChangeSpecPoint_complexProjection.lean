-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizationIntegerBaseChangeSpecPoint_complexProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:44:50.475142+00:00
-- url     : https://prove2.me/submissions/7ee7b822-2261-4a72-898e-dabac4ab34a2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationOverlapEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationComplexPoints
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationCurveSpecPoint_overC
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalToIntegerBaseChange_complexProjection


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
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x : LPSOriginalFilledCurve N) :
    lpsOriginalNormalizationIntegerBaseChangeSpecPoint N hpos hN x ≫ pullback.fst _ _ = 𝟙 _ := by
  change (lpsOriginalNormalizationCurveSpecPoint N hpos hN x ≫
    lpsOriginalComplexNormalToIntegerBaseChange N hpos) ≫ _ = _
  rw [Category.assoc, lpsOriginalComplexNormalToIntegerBaseChange_complexProjection]
  exact lpsOriginalNormalizationCurveSpecPoint_overC N hpos hN x
end QEC.Coding.TannerLiftedProduct
