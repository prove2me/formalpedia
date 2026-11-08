-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.adjacencyGraph_expanding_of_doubleCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:20:57.342176+00:00
-- url     : https://prove2.me/submissions/92d457cf-49a8-4dd0-8c98-806b0be1908c

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalGraph_eq_relabel_disjointUnion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalGraph_eq_relabel_disjointUnion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_adjacencyGraph_eq_add
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_leftDoubleCoverGraph_expanding
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_add
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_disjointUnion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_relabel
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add


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
    (hLambda : 0 ≤ lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radius (2 * lambda) := by
  have hHorizontal : SmallSetExpansion.IsSmallSetEdgeExpanding
      (horizontalGraph label) radius lambda := by
    rw [horizontalGraph_eq_relabel_disjointUnion]
    exact (SmallSetExpansion.IsSmallSetEdgeExpanding.disjointUnion
      hLambda (fun _ => hBase)).relabel horizontalFiberEquiv
  have hVertical : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalGraph label) radius lambda := by
    rw [verticalGraph_eq_relabel_disjointUnion]
    exact (SmallSetExpansion.IsSmallSetEdgeExpanding.disjointUnion
      hLambda (fun _ => leftDoubleCoverGraph_expanding label radius lambda hBase)).relabel
        verticalFiberEquiv
  rw [adjacencyGraph_eq_add, show (2 : ℝ) * lambda = lambda + lambda by ring]
  exact hHorizontal.add hVertical
end QEC.Coding.TannerLiftedProduct
