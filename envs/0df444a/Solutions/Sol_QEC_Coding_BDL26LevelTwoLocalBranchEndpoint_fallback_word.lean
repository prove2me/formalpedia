-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.fallback_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:09:10.397527+00:00
-- url     : https://prove2.me/submissions/ad099182-37d8-4ae9-b522-a6517ff21076

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical
namespace QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
theorem _root_.solution (S : OddScale) (t : Syndrome S) (hn : localSearch S t=none) :
    D S t=BDL26LevelTwoDecoder.toActualError S ((globalSearch S t).getD 0) := by
  unfold localSearch at hn
  unfold D BDL26LevelTwoDecoder.decode BDL26LevelTwoDecoder.executableDecode
    BDL26LevelTwoDecoder.lookup globalSearch
  rw [hn]
end QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
