-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.compactToLocal_representative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:00:34.570654+00:00
-- url     : https://prove2.me/submissions/ef12996f-5193-4b1e-afe3-55c27bef86bf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLocalChartGermTopology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (x : LPSOriginalFilledCurve N)
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN) :
    lpsOriginalCompactToLocal N hN x ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F) =
      lpsOriginalRepresentativeToLocal N hN x F :=
  RingHom.liftOfSurjective_comp_apply _ _ _ _
end QEC.Coding.TannerLiftedProduct
