-- Prove2me | solution 1 for QEC.Coding.BDL26QuantitativeBounds.rzFace_card_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:31:54.453726+00:00
-- url     : https://prove2.me/submissions/7c606923-216d-4bf8-89e9-843d6255a19e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_rxFace_card_upper

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph
namespace QEC.Coding.BDL26QuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) :
    Fintype.card (BDL26RZLocalReplacement.RZFace P S) ≤
      faceGrowthFactor S * Fintype.card P.Face := by
  rw [Fintype.card_congr (rzFaceEquiv P S)]
  exact rxFace_card_upper (transposePresentation P) S
end QEC.Coding.BDL26QuantitativeBounds
