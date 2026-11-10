-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoCode.levelTwoQ_card_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:45:57.79344+00:00
-- url     : https://prove2.me/submissions/be06e2c4-5231-4a00-99f0-0faa3e450b40

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_state_qubit_card_upper


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators
namespace QEC.Coding.BDL26LevelTwoCode
theorem _root_.solution (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Q ≤
      8 * (2 * S.ell * (S.ell + 2)) ^ 2 :=
  state_qubit_card_upper S 2
end QEC.Coding.BDL26LevelTwoCode
