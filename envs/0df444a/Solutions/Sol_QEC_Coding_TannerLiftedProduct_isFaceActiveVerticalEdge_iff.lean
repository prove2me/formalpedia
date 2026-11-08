-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.isFaceActiveVerticalEdge_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:59:21.931195+00:00
-- url     : https://prove2.me/submissions/633032c0-c3d0-44d9-8693-aa9558a2f408

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq G] [Fintype W] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G) :
    IsFaceActiveVerticalEdge label c e ↔
      CarriesActiveFaceVerticalEdge label c e ∧
      verticalEdgeEndpoint label e 0 ∉ vertexBlockSupport c ∧
      verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1 ∉
        vertexBlockSupport c := by
  rfl
end QEC.Coding.TannerLiftedProduct
