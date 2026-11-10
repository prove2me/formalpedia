-- Prove2me | solution 1 for QEC.Coding.BDL26QuantitativeBounds.nextState_qubit_card_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:21:08.005521+00:00
-- url     : https://prove2.me/submissions/93567ef3-2d49-4f94-af66-9e9e779a0c66

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_rxQubit_card_lower
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_rzQubit_card_lower

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph
namespace QEC.Coding.BDL26QuantitativeBounds
theorem _root_.solution (S : OddScale) (n : Nat) (C : ConstructionState) :
    2 * Fintype.card C.presentation.Q ≤
      Fintype.card (nextState S n C).presentation.Q := by
  unfold nextState
  split
  · exact rxQubit_card_lower C.presentation S
  · calc
      2 * Fintype.card C.presentation.Q ≤
          Fintype.card (BDL26RZLocalReplacement.RZQ C.presentation S) :=
        rzQubit_card_lower C.presentation S
      _ = Fintype.card (rzState S C).presentation.Q :=
        Fintype.card_congr (Equiv.refl _)
end QEC.Coding.BDL26QuantitativeBounds
