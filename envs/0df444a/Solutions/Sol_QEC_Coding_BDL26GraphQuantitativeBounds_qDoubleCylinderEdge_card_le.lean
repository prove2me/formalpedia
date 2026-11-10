-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.qDoubleCylinderEdge_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:49:17.002242+00:00
-- url     : https://prove2.me/submissions/12de71f2-b665-482d-870a-6248e6e7d43f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_qDoubleCylinderEdge_card


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation)
    (h : BoundedValence P) (q : P.Q) (S : OddScale) :
    Fintype.card (QDoubleCylinderEdge P q S) ≤ localCoordinateBound S := by
  have hd : Fintype.card (QStarEdge P q) ≤4 := (h.2.2 q).2.1
  have hm := Nat.mul_le_mul_right S.ell hd
  have hs := S.three_le
  rw [qDoubleCylinderEdge_card]
  unfold localCoordinateBound
  nlinarith
end QEC.Coding.BDL26GraphQuantitativeBounds
