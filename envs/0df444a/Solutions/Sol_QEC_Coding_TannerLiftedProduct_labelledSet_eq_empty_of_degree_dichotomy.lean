-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.labelledSet_eq_empty_of_degree_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:51:18.283096+00:00
-- url     : https://prove2.me/submissions/3688a718-fbf9-4dcb-8fa5-9fb95713a250

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_labelledSet_eq_empty


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype G] [DecidableEq W]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (L : Finset (VertexIndex G))
    (radiusEdge radiusFace m s : Nat) (lambdaEdge lambdaFace : ℝ)
    (hLambdaEdge : 0 < lambdaEdge) (hLambdaFace : 0 < lambdaFace)
    (hExpandEdge : SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radiusEdge lambdaEdge)
    (hExpandFace : SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radiusFace lambdaFace)
    (hLRadiusEdge : L.card ≤ radiusEdge)
    (hLRadiusFace : L.card ≤ radiusFace)
    (hDichotomy : ∀ v ∈ L,
      m ≤ ∑ u ∈ L, adjacencyGraph label v u ∨
        s ≤ ∑ u ∈ L, faceSquareGraph label v u)
    (hThresholdEdge : 2 * lambdaEdge ≤ m)
    (hThresholdFace : 2 * lambdaFace ≤ s) :
    L = ∅ := by
  let LEdge := edgeExpandingVertices label L m
  let LFace := faceExpandingVertices label L s
  apply SmallSetExpansion.labelledSet_eq_empty
    (adjacencyGraph label) (faceSquareGraph label)
    radiusEdge radiusFace m s lambdaEdge lambdaFace
    hLambdaEdge hLambdaFace hExpandEdge hExpandFace L LEdge LFace
  · intro v hv
    rcases hDichotomy v hv with hEdge | hFace
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hv, hEdge⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hv, hFace⟩)
  · exact Finset.filter_subset _ _
  · exact Finset.filter_subset _ _
  · exact hLRadiusEdge
  · exact hLRadiusFace
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · exact hThresholdEdge
  · exact hThresholdFace
end QEC.Coding.TannerLiftedProduct
