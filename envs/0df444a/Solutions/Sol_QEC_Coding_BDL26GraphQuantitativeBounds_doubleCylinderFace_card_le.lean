-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.doubleCylinderFace_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:45:47.228672+00:00
-- url     : https://prove2.me/submissions/aca7606b-851c-4e5e-8a96-36165b139fe7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_xStarFace_card_le
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_xStarBoundaryEdge_card_le
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_OddScale_two_half_add_one
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_doubleCylinderFace_card


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation)
    (h : BoundedValence P) (x : P.X) (S : OddScale) :
    Fintype.card (DoubleCylinderFace P x S) ≤ localCoordinateBound S := by
  have hf := Nat.mul_le_mul_right (S.half^2) (xStarFace_card_le P h x)
  have hb := Nat.mul_le_mul_right S.half (xStarBoundaryEdge_card_le P h x)
  rw [doubleCylinderFace_card]
  unfold localCoordinateBound
  rw [←S.two_half_add_one]
  nlinarith
end QEC.Coding.BDL26GraphQuantitativeBounds
