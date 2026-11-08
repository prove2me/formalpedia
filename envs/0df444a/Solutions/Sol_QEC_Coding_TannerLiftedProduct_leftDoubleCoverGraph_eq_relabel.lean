-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.leftDoubleCoverGraph_eq_relabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:15:11.415481+00:00
-- url     : https://prove2.me/submissions/3a94a224-7fd8-4499-a2e2-7944721901ea

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_leftDoubleCoverNeighbor
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_relabel


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G] [DecidableEq W]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (label : W → G) :
    leftDoubleCoverGraph label =
      SmallSetExpansion.relabel sideInverseEquiv
        (rightDoubleCoverGraph label) := by
  funext x y
  unfold leftDoubleCoverGraph rightDoubleCoverGraph
  change (Finset.univ.filter fun a : W =>
      leftDoubleCoverNeighbor label x a = y).card =
    (Finset.univ.filter fun a : W =>
      rightDoubleCoverNeighbor label (sideInverseEquiv x) a =
        sideInverseEquiv y).card
  congr 1
  apply Finset.filter_congr
  intro a _ha
  constructor
  · intro hxy
    rw [← sideInverseEquiv_leftDoubleCoverNeighbor]
    exact congrArg sideInverseEquiv hxy
  · intro hxy
    apply sideInverseEquiv.injective
    rw [sideInverseEquiv_leftDoubleCoverNeighbor]
    exact hxy
end QEC.Coding.TannerLiftedProduct
