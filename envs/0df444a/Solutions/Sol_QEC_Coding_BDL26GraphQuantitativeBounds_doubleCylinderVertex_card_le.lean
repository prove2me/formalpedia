-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.doubleCylinderVertex_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:09:52.765111+00:00
-- url     : https://prove2.me/submissions/634bfe52-88bb-4ebc-9985-d60299b85e3e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_xStarFace_card_le
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_xStarVertex_card_le
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_xStarEdge_card_le
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_OddScale_two_half_add_one
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_doubleCylinderVertex_card


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (h : BoundedValence P) (x : P.X) (S : OddScale) :
    Fintype.card (DoubleCylinderVertex P x S) ≤ localCoordinateBound S := by
  have hv := xStarVertex_card_le P A h x
  have he := Nat.mul_le_mul_right (S.half-1) (xStarEdge_card_le P h x)
  have hf := Nat.mul_le_mul_right ((S.half-1)*(S.half-1)) (xStarFace_card_le P h x)
  have hm : S.half-1+1=S.half := by have hp:=S.half_pos; omega
  rw [doubleCylinderVertex_card]
  unfold localCoordinateBound
  rw [←S.two_half_add_one]
  nlinarith
end QEC.Coding.BDL26GraphQuantitativeBounds
