-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.localFaceMatrix_mul_transpose_eq_verticalEndpointSyndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:50:45.662195+00:00
-- url     : https://prove2.me/submissions/a59509aa-1057-4773-a225-e511b74eeb09

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary1_verticalEdge_matrix_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hc : LiftedProduct.boundary1 (data label h h') c = 0)
    (v : VertexIndex G) :
    localFaceMatrix label c v * h.transpose =
      verticalEndpointSyndrome label h' c v := by
  ext b r
  have hedge := congrFun hc (verticalEdgeCoordinate label v r b)
  rw [boundary1_verticalEdge_matrix_apply] at hedge
  exact sub_eq_zero.mp hedge
end QEC.Coding.TannerLiftedProduct
