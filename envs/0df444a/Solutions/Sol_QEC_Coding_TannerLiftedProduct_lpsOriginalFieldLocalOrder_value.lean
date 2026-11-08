-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLocalOrder_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:59:59.01846+00:00
-- url     : https://prove2.me/submissions/b47e2964-eef6-428e-b210-305740612bf0

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
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (hpos : 0 < N) (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∀ f : lpsOriginalGeneratedFunctionField N hpos,
      lpsOriginalFieldLocalOrder N hN hpos x f =
        meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x) (lpsOriginalFieldToLocal N hN hpos x f) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  intro f
  rfl
end QEC.Coding.TannerLiftedProduct
