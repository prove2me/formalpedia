-- Prove2me | solution 1 for QEC.Coding.BDL26QuantitativeBounds.evenState_qubit_card_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:56:16.291082+00:00
-- url     : https://prove2.me/submissions/4b2200ec-546b-43f8-b390-583685e8c996

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_state_qubit_card_lower
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_state_qubit_card_upper

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph
namespace QEC.Coding.BDL26QuantitativeBounds
theorem _root_.solution (S : OddScale) (k : Nat) :
    5 * 2 ^ (2 * k) ≤ Fintype.card (state S (2 * k)).presentation.Q ∧
    Fintype.card (state S (2 * k)).presentation.Q ≤
      8 * (2 * S.ell * (S.ell + 2)) ^ (2 * k) :=
  ⟨state_qubit_card_lower S (2 * k), state_qubit_card_upper S (2 * k)⟩
end QEC.Coding.BDL26QuantitativeBounds
