-- Prove2me | solution 1 for QEC.Coding.BDL26QuantitativeBounds.nextState_face_card_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:35:08.197199+00:00
-- url     : https://prove2.me/submissions/c7141657-4a59-4eaf-8a4f-c6f3069653bb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_rxFace_card_upper
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_rzFace_card_upper

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph
namespace QEC.Coding.BDL26QuantitativeBounds
theorem _root_.solution (S : OddScale) (n : Nat) (C : ConstructionState) :
    Fintype.card (nextState S n C).presentation.Face ≤
      faceGrowthFactor S * Fintype.card C.presentation.Face := by
  unfold nextState
  split
  · exact rxFace_card_upper C.presentation S
  · calc
      Fintype.card (rzState S C).presentation.Face =
          Fintype.card (BDL26RZLocalReplacement.RZFace C.presentation S) :=
        Fintype.card_congr (Equiv.refl _)
      _ ≤ faceGrowthFactor S * Fintype.card C.presentation.Face :=
        rzFace_card_upper C.presentation S
end QEC.Coding.BDL26QuantitativeBounds
