-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFieldToLocal_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:04:08.735664+00:00
-- url     : https://prove2.me/submissions/a2881c6b-de28-4705-b847-5f588a82f9c6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_compactToLocal_representative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv_j


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
theorem _root_.solution (x : LPSOriginalFilledCurve N) :
    lpsOriginalFieldToLocal N hN hpos x (algebraMap P K Polynomial.X) =
      lpsOriginalRepresentativeToLocal N hN x
        ⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩ := by
  change lpsOriginalCompactToLocal N hN x
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN
      (algebraMap P K Polynomial.X)) = _
  rw [lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv_j]
  exact compactToLocal_representative N hN x _
end QEC.Coding.TannerLiftedProduct
