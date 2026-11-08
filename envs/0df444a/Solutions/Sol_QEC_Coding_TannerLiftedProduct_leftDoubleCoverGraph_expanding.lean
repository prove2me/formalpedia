-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.leftDoubleCoverGraph_expanding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:18:39.522884+00:00
-- url     : https://prove2.me/submissions/eae75bf1-e30c-4429-b6c6-44c8957ee4f8

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_leftDoubleCoverGraph_eq_relabel
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_relabel


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G] [DecidableEq W]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (leftDoubleCoverGraph label) radius lambda := by
  rw [leftDoubleCoverGraph_eq_relabel]
  exact hBase.relabel sideInverseEquiv
end QEC.Coding.TannerLiftedProduct
