-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.adjacencySquare_expanding_of_doubleCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:24:33.148203+00:00
-- url     : https://prove2.me/submissions/3bcdbcf5-4543-4bd5-ad55-cc584c0fdf1b

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_adjacencyGraph_isSymmetric
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_adjacencyGraph_isRegular
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_adjacencyGraph_expanding_of_doubleCover
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_square_of_symmetric_regular


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
    (hLambda : 0 ≤ lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (SmallSetExpansion.square (adjacencyGraph label))
      (radius / (2 * Fintype.card W))
      (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) := by
  have hProduct := adjacencyGraph_expanding_of_doubleCover
    label radius lambda hLambda hBase
  have hSquare :=
    SmallSetExpansion.IsSmallSetEdgeExpanding.square_of_symmetric_regular
      (M := adjacencyGraph label) (degree := 2 * Fintype.card W)
      (lambda := 2 * lambda) (by positivity)
      (adjacencyGraph_isSymmetric label)
      (adjacencyGraph_isRegular label) hProduct
  convert hSquare using 1
  ring
end QEC.Coding.TannerLiftedProduct
