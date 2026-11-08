-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLocalOrder_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:07:07.887651+00:00
-- url     : https://prove2.me/submissions/4cf42fbf-9213-4466-9e48-a43562cb6968

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_meromorphicOrderValuation_eq_top_iff


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
    ∀ f : lpsOriginalGeneratedFunctionField N hpos, f ≠ 0 →
      lpsOriginalFieldLocalOrder N hN hpos x f ≠ ⊤ := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  intro f hf htop
  have hlocal : lpsOriginalFieldToLocal N hN hpos x f = 0 :=
    (meromorphicOrderValuation_eq_top_iff _ _).mp htop
  apply hf
  exact (lpsOriginalFieldToLocal N hN hpos x).injective
    (hlocal.trans (map_zero _).symm)
end QEC.Coding.TannerLiftedProduct
