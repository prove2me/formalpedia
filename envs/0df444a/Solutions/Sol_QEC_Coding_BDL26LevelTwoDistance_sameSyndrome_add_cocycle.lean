-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.sameSyndrome_add_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:28:52.373203+00:00
-- url     : https://prove2.me/submissions/1e2c0852-f685-41ad-a28e-09411039eb37

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
namespace QEC.Coding.BDL26LevelTwoDistance
theorem _root_.solution (S : OddScale)
    (first second : Word Field (levelTwoPresentation S).Q)
    (h : tannerCoboundary1 (levelTwoPresentation S) first =
      tannerCoboundary1 (levelTwoPresentation S) second) :
    tannerCoboundary1 (levelTwoPresentation S) (first + second) = 0 := by
  rw [map_add, h]
  exact ZModModule.add_self _
end QEC.Coding.BDL26LevelTwoDistance
