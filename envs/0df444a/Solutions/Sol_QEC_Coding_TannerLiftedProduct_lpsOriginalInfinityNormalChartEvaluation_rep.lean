-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityNormalChartEvaluation_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:29:19.197236+00:00
-- url     : https://prove2.me/submissions/b36bb291-25e2-4c01-bdfa-3fc7c6935795

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_meromorphicNoPoleEvaluation_rep
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
    (a : lpsOriginalComplexNormalInfinityChart N hpos)
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g (lpsOriginalLocalChartCenter N hN x))
    (he : F.val ∘ (lpsOriginalLocalChart N hN x).symm =ᶠ[𝓝[≠] lpsOriginalLocalChartCenter N hN x] g) :
    lpsOriginalInfinityNormalChartEvaluation N hpos hN x hj a = g (lpsOriginalLocalChartCenter N hN x) := by
  apply meromorphicNoPoleEvaluation_rep _ _ g hg
  change (lpsOriginalFieldToLocal N hN hpos x a.val).val =
    (g : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ)
  rw [lpsOriginalFieldToLocal_representative N hN hpos x a.val F hF]
  change (F.val ∘ (lpsOriginalLocalChart N hN x).symm : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ) =
    (g : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ)
  exact Filter.Germ.coe_eq.mpr he
end QEC.Coding.TannerLiftedProduct
