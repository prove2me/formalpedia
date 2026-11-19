-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_sameChainSyndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:55:15.002354+00:00
-- url     : https://prove2.me/submissions/657ff732-1518-4be7-ad95-bc7d7525a3a6

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_sameSyndrome

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph
namespace QEC.Coding.BDL26LevelTwoDistance
theorem _root_.solution (S : OddScale)
    (first second : Word Field (levelTwoPresentation S).Q)
    (hfirst : levelTwoLocalError S first) (hsecond : levelTwoLocalError S second)
    (hsyn : wordLinearMapTranspose (levelTwoChainComplex S).boundary2 first =
      wordLinearMapTranspose (levelTwoChainComplex S).boundary2 second) :
    first + second ∈ (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by
  rw [levelTwo_coboundary1_eq] at hsyn
  exact levelTwoLocalError_sameSyndrome S first second hfirst hsecond hsyn
end QEC.Coding.BDL26LevelTwoDistance
