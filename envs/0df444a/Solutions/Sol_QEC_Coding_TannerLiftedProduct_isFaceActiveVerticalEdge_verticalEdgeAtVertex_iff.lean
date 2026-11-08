-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.isFaceActiveVerticalEdge_verticalEdgeAtVertex_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:14:37.824524+00:00
-- url     : https://prove2.me/submissions/b3b7064a-e361-4331-a863-a1b380bb67b5

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_isFaceActiveVerticalEdge_iff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_carriesActiveFaceVerticalEdge_verticalEdgeAtVertex_iff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalEdgeAtVertex_canonicalEndpoints_mem_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [Fintype W] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W) :
    IsFaceActiveVerticalEdge label c (verticalEdgeAtVertex label v b) ↔
      IsFaceActiveVerticalEdgeAt label c v b := by
  rw [isFaceActiveVerticalEdge_iff,
    carriesActiveFaceVerticalEdge_verticalEdgeAtVertex_iff]
  unfold IsFaceActiveVerticalEdgeAt
  have hEndpoints := verticalEdgeAtVertex_canonicalEndpoints_mem_iff
    label (vertexBlockSupport c) v b
  tauto
end QEC.Coding.TannerLiftedProduct
