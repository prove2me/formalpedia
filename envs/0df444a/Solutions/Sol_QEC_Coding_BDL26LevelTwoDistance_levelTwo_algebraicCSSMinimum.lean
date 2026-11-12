-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.levelTwo_algebraicCSSMinimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:02:21.639669+00:00
-- url     : https://prove2.me/submissions/ad633a71-e80a-40e9-92ca-d1369762eb13

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwo_pureXMinimum
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwo_pureZMinimum
import Theorems.Thm_QEC_Coding_algebraicCSSMinimumDistance_of_sector_minima


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph
namespace QEC.Coding.BDL26LevelTwoDistance
theorem _root_.solution (S : OddScale) :
    AlgebraicCSSMinimumDistance (levelTwoXCode S) (levelTwoZCode S)
      (min (levelTwoXDistance S) (levelTwoZDistance S)) :=
  algebraicCSSMinimumDistance_of_sector_minima
    (levelTwo_pureXMinimum S) (levelTwo_pureZMinimum S)
end QEC.Coding.BDL26LevelTwoDistance
