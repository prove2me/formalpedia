-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.faceSquareGraph_expanding_of_doubleCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:29:07.165557+00:00
-- url     : https://prove2.me/submissions/867d68ec-6bb4-4adc-9237-38a9f38593af

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_adjacencySquare_expanding_of_doubleCover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceSquareGraph_expanding_of_adjacencySquare

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
      (faceSquareGraph label) (radius / (2 * Fintype.card W))
      (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) :=
  faceSquareGraph_expanding_of_adjacencySquare label _ _
    (adjacencySquare_expanding_of_doubleCover
      label radius lambda hLambda hBase)
end QEC.Coding.TannerLiftedProduct
