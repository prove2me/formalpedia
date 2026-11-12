-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoCode.levelTwo_graph_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:58:51.060203+00:00
-- url     : https://prove2.me/submissions/234da222-3151-4746-82b4-1c3914655db5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators
namespace QEC.Coding.BDL26LevelTwoCode
theorem _root_.solution (S : OddScale) :
    level S 3 = tannerLevel (levelTwoPresentation S) := rfl
end QEC.Coding.BDL26LevelTwoCode
