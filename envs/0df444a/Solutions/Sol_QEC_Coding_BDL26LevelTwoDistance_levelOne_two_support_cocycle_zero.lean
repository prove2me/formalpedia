-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.levelOne_two_support_cocycle_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:34:08.703307+00:00
-- url     : https://prove2.me/submissions/5aa699f6-42f6-4856-9f46-19ba5f3075cc

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_seedRX_two_support_cocycle_zero
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary1_eq


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
    (word : Word Field (levelOnePresentation S).Q)
    (hc : tannerCoboundary1 (levelOnePresentation S) word = 0)
    (a b : (levelOnePresentation S).Q)
    (hsupport : ∀ c, word c ≠ 0 → c = a ∨ c = b) : word = 0 := by
  change tannerCoboundary1 (rxReplacementPresentation baseTannerSquarePresentation S) word = 0 at hc
  erw [rxPresentation_coboundary1_eq baseTannerSquarePresentation baseTannerSquareAdmissibleV4
    baseTannerSquareCellularRegular S] at hc
  exact seedRX_two_support_cocycle_zero S word hc a b hsupport
end QEC.Coding.BDL26LevelTwoDistance
