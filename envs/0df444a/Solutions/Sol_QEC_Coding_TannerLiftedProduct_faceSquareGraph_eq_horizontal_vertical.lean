-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.faceSquareGraph_eq_horizontal_vertical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:15:05.113501+00:00
-- url     : https://prove2.me/submissions/8cfbb8c1-3bf5-4fc1-857b-16036d615218

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_card_filter_product_eq_sum_card_fibers


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [DecidableEq W]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (label : W → G)
    (v u : VertexIndex G) :
    faceSquareGraph label v u =
      ∑ x, horizontalGraph label v x * verticalGraph label x u := by
  unfold faceSquareGraph horizontalGraph verticalGraph
  exact SmallSetExpansion.card_filter_product_eq_sum_card_fibers
    (fun a : W => horizontalNeighbor label v a)
    (fun x : VertexIndex G => fun b : W => verticalNeighbor label x b) u
end QEC.Coding.TannerLiftedProduct
