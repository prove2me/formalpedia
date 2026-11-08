-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLocalOrder_constant_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:05:55.775676+00:00
-- url     : https://prove2.me/submissions/3db947bd-12eb-41b6-85c8-d37acb3db200

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_constant

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
    (x : LPSOriginalFilledCurve N) (c : ℂ) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap ℂ K c) := by
  rw [lpsOriginalFieldLocalOrder_value, lpsOriginalFieldToLocal_constant]
  change 0 ≤ meromorphicOrderAt (fun _ : ℂ => c) (lpsOriginalLocalChartCenter N hN x)
  exact (MeromorphicAt.const c _).meromorphicOrderAt_nonneg_iff.mpr
    ⟨fun _ => c, analyticAt_const, Filter.EventuallyEq.rfl⟩
end QEC.Coding.TannerLiftedProduct
