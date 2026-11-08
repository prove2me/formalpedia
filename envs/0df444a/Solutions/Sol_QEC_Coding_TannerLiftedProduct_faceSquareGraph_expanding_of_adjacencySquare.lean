-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.faceSquareGraph_expanding_of_adjacencySquare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:25:37.429622+00:00
-- url     : https://prove2.me/submissions/d662d587-61a6-4c27-b733-167842c470c4

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceSquareGraph_le_adjacencyGraph_square
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_of_pointwise_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [DecidableEq W]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hSquare : SmallSetExpansion.IsSmallSetEdgeExpanding
      (SmallSetExpansion.square (adjacencyGraph label)) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radius lambda :=
  hSquare.of_pointwise_le (faceSquareGraph_le_adjacencyGraph_square label)
end QEC.Coding.TannerLiftedProduct
