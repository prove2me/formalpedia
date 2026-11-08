-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.faceSquareGraph_le_adjacencyGraph_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:22:35.150207+00:00
-- url     : https://prove2.me/submissions/02023716-ae7b-425c-aa91-e7ac648643a0

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceSquareGraph_eq_horizontal_vertical

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
    faceSquareGraph label v u ≤
      SmallSetExpansion.square (adjacencyGraph label) v u := by
  rw [faceSquareGraph_eq_horizontal_vertical]
  unfold SmallSetExpansion.square
  apply Finset.sum_le_sum
  intro x _hx
  apply Nat.mul_le_mul
  · exact Nat.le_add_right
      (horizontalGraph label v x) (verticalGraph label v x)
  · exact Nat.le_add_left
      (verticalGraph label x u) (horizontalGraph label x u)
end QEC.Coding.TannerLiftedProduct
