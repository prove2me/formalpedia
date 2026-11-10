-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.zCylinder_cycle_has_filling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:26:28.031574+00:00
-- url     : https://prove2.me/submissions/3d2da86b-1051-423d-aa87-b49da48d5c5a

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_xCylinder_boundary_eq_cycle

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph
namespace QEC.Coding.BDL26LevelTwoDistance
theorem _root_.solution (P : TannerSquarePresentation)
    (A3 : TannerSquareAdmissibleV3 P) (R : TannerSquareCellularRegular P)
    (z : P.Z) (S : OddScale) (word : Word Field (ZDoubleCylinderEdge P z S))
    (hword : doubleCylinderBoundary1 (transposePresentation P) z S word = 0) :
    ∃ faces : Word Field (ZDoubleCylinderFace P z S),
      doubleCylinderBoundary2 (transposePresentation P) z S faces = word := by
  have hm : word ∈ (rxCx (transposePresentation P) z S).middleCycleCode.carrier :=
    ((rxCx (transposePresentation P) z S).mem_middleCycleCode_iff word).2 hword
  rw [← xCylinder_boundary_eq_cycle (transposePresentation P)
    (transposeTannerSquareAdmissibleV3 P A3) (transposeTannerSquareCellularRegular P R)
    z S] at hm
  exact ((rxCx (transposePresentation P) z S).mem_middleBoundaryCode_iff word).1 hm
end QEC.Coding.BDL26LevelTwoDistance
