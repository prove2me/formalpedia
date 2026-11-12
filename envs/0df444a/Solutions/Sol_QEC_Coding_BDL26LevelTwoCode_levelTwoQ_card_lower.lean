-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoCode.levelTwoQ_card_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:58:17.059769+00:00
-- url     : https://prove2.me/submissions/03fac4e5-64c4-4d5b-a6c2-b86ae47af278

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_state_qubit_card_lower


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators
namespace QEC.Coding.BDL26LevelTwoCode
theorem _root_.solution (S : OddScale) :
    20 ≤ Fintype.card (levelTwoPresentation S).Q := by
  have h := state_qubit_card_lower S 2
  norm_num only at h
  exact h
end QEC.Coding.BDL26LevelTwoCode
