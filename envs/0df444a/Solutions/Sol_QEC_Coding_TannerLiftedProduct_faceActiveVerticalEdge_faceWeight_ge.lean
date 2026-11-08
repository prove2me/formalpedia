-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.faceActiveVerticalEdge_faceWeight_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:14:32.479222+00:00
-- url     : https://prove2.me/submissions/e4236c89-7451-481f-8a7f-cdf72b07b068

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_isFaceActiveVerticalEdge_iff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceMatrix_row_mem_parityCheckCode_of_faceActive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceMatrix_row_ne_zero_of_carriesActiveFace

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
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (e : VerticalEdgeIndex W G)
    (he : IsFaceActiveVerticalEdge label c e) :
    d ≤ HammingWeight
      (ProductExpansion.row
        (localFaceMatrix label c (verticalEdgeEndpoint label e 0)) e.2.1) := by
  apply hDistance
  · exact localFaceMatrix_row_mem_parityCheckCode_of_faceActive
      label h g' c hcCycle e he
  · exact localFaceMatrix_row_ne_zero_of_carriesActiveFace
      label c e ((isFaceActiveVerticalEdge_iff label c e).mp he).1
end QEC.Coding.TannerLiftedProduct
