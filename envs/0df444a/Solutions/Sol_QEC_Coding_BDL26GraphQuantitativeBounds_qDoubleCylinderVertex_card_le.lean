-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.qDoubleCylinderVertex_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:24:18.979509+00:00
-- url     : https://prove2.me/submissions/50ce502c-187e-4946-a428-ae8a80c20f1b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_OddScale_two_half_add_one
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_qDoubleCylinderVertex_card


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation)
    (h : BoundedValence P) (q : P.Q) (S : OddScale) :
    Fintype.card (QDoubleCylinderVertex P q S) ≤ localCoordinateBound S := by
  have hd : Fintype.card (QStarEdge P q) ≤4 := (h.2.2 q).2.1
  have hm := Nat.mul_le_mul_right S.half hd
  rw [qDoubleCylinderVertex_card]
  unfold localCoordinateBound
  rw [←S.two_half_add_one]
  nlinarith
end QEC.Coding.BDL26GraphQuantitativeBounds
