-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalZeroIntegral_analytic_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:24:47.006084+00:00
-- url     : https://prove2.me/submissions/bcf19101-6046-4207-bc1f-dd622eef37b6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_integral_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_representative

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLocalChartGermTopology
variable (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_125
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_131
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_132
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_133
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_135
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_136
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (a : integralClosure P K) :
    ∃ F : LPSOriginalFilledMeromorphicFunctionRing N hN,
      lpsOriginalCompactMeromorphicGermAlgHom N hN F =
        lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g (lpsOriginalLocalChartCenter N hN x) ∧
        F.val ∘ (lpsOriginalLocalChart N hN x).symm =ᶠ[𝓝[≠] lpsOriginalLocalChartCenter N hN x] g := by
  obtain ⟨F,hF⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val)
  refine ⟨F,hF,?_⟩
  have hv := lpsOriginalFieldLocalOrder_integral_nonnegative N hN hpos x hj a
  rw [lpsOriginalFieldLocalOrder_value,
    lpsOriginalFieldToLocal_representative N hN hpos x a.val F hF] at hv
  change 0 ≤ meromorphicOrderAt (F.val ∘ (lpsOriginalLocalChart N hN x).symm)
    (lpsOriginalLocalChartCenter N hN x) at hv
  exact (F.property x _ ((lpsOriginalLocalChart N hN x).map_source
    (lpsOriginalLocalChart_mem_source N hN x))).meromorphicOrderAt_nonneg_iff.mp hv
end QEC.Coding.TannerLiftedProduct
