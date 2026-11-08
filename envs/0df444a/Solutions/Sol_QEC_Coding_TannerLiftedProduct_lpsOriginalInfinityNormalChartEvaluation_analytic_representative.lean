-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityNormalChartEvaluation_analytic_representative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:44:11.65003+00:00
-- url     : https://prove2.me/submissions/6d1bdbc1-fb66-4776-a71e-e1b6ee05a4aa

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityNormalChartEvaluation_rep
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_representative


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
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (a : lpsOriginalComplexNormalInfinityChart N hpos) :
    ∃ F : LPSOriginalFilledMeromorphicFunctionRing N hN,
      lpsOriginalCompactMeromorphicGermAlgHom N hN F =
        lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g (lpsOriginalLocalChartCenter N hN x) ∧
        F.val ∘ (lpsOriginalLocalChart N hN x).symm =ᶠ[𝓝[≠] lpsOriginalLocalChartCenter N hN x] g ∧
        lpsOriginalInfinityNormalChartEvaluation N hpos hN x hj a = g (lpsOriginalLocalChartCenter N hN x) := by
  obtain ⟨F,hF⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val)
  have hv := lpsOriginalInfinityIntegral_order_nonnegative N hpos hN x hj a
  rw [lpsOriginalFieldLocalOrder_value,
    lpsOriginalFieldToLocal_representative N hN hpos x a.val F hF] at hv
  change 0 ≤ meromorphicOrderAt (F.val ∘ (lpsOriginalLocalChart N hN x).symm)
    (lpsOriginalLocalChartCenter N hN x) at hv
  obtain ⟨g,hg,he⟩ := (F.property x _ ((lpsOriginalLocalChart N hN x).map_source
    (lpsOriginalLocalChart_mem_source N hN x))).meromorphicOrderAt_nonneg_iff.mp hv
  exact ⟨F,hF,g,hg,he,lpsOriginalInfinityNormalChartEvaluation_rep N hpos hN x hj a F hF g hg he⟩
end QEC.Coding.TannerLiftedProduct
