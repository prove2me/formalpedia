-- Prove2me | solution 1 for QEC.Coding.BDL26QuantitativeBounds.state_qubit_card_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:42:23.898091+00:00
-- url     : https://prove2.me/submissions/0e3c7695-cf16-4763-8d59-b527141f0728

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_qubit_card_le_twice_face
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_state_face_card_upper

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph
namespace QEC.Coding.BDL26QuantitativeBounds
theorem _root_.solution (S : OddScale) (n : Nat) :
    Fintype.card (state S n).presentation.Q ≤ 8 * faceGrowthFactor S ^ n := by
  calc
    _ ≤ 2 * Fintype.card (state S n).presentation.Face :=
      qubit_card_le_twice_face _ (state S n).admissible.toTannerSquareAdmissible
    _ ≤ 2 * (4 * faceGrowthFactor S ^ n) :=
      Nat.mul_le_mul_left _ (state_face_card_upper S n)
    _ = 8 * faceGrowthFactor S ^ n := by ring
end QEC.Coding.BDL26QuantitativeBounds
