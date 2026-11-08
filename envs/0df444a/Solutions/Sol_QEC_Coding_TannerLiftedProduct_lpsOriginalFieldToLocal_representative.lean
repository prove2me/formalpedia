-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFieldToLocal_representative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:05:18.396871+00:00
-- url     : https://prove2.me/submissions/2759dbf7-f6ce-4e58-bb87-b2c3fbe6a0b4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_compactToLocal_representative

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
theorem _root_.solution (x : LPSOriginalFilledCurve N)
    (f : K) (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) :
    lpsOriginalFieldToLocal N hN hpos x f = lpsOriginalRepresentativeToLocal N hN x F := by
  change lpsOriginalCompactToLocal N hN x
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) = _
  rw [← hF]
  exact compactToLocal_representative N hN x F
end QEC.Coding.TannerLiftedProduct
