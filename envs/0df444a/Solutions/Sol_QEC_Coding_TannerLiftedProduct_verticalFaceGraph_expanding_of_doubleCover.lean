-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.verticalFaceGraph_expanding_of_doubleCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:22:33.586381+00:00
-- url     : https://prove2.me/submissions/cc37e5d8-5f2c-4afe-9039-f3418629d362

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalFaceGraph_eq_relabel_disjointUnion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_disjointUnion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_relabel


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hLambda : 0 ≤ lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radius lambda := by
  rw [verticalFaceGraph_eq_relabel_disjointUnion]
  exact (SmallSetExpansion.IsSmallSetEdgeExpanding.disjointUnion
    hLambda (fun _ => hBase)).relabel verticalEdgeFiberEquiv
end QEC.Coding.TannerLiftedProduct
