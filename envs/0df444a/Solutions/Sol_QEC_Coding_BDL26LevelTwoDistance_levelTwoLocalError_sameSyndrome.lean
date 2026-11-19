-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_sameSyndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:39:00.257646+00:00
-- url     : https://prove2.me/submissions/99529db1-93b4-471b-89af-18bd31f57091

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_sameSyndrome_add_cocycle
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzCocycle_qParity_zero_is_coboundary
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_cocycle
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_add_qParity_two_coordinates
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelOne_two_support_cocycle_zero

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
    (hsyn : tannerCoboundary1 (levelTwoPresentation S) first =
      tannerCoboundary1 (levelTwoPresentation S) second) :
    first + second ∈ (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by
  have hc := sameSyndrome_add_cocycle S first second hsyn
  have hprojected := rzQParity_cocycle (levelOnePresentation S)
    (rxState S baseState).admissible S (first + second) hc
  obtain ⟨a, b, hab⟩ := levelTwoLocalError_add_qParity_two_coordinates S
    (levelOneQDefault S) first second hfirst hsecond
  have hparity := levelOne_two_support_cocycle_zero S
    (rzQParity (levelOnePresentation S) S (first + second)) hprojected a b hab
  obtain ⟨potential, hp⟩ := rzCocycle_qParity_zero_is_coboundary (levelOnePresentation S)
    (rxState S baseState).admissible (rxState S baseState).regular S (first + second) hc hparity
  apply ((levelTwoChainComplex S).mem_firstCoboundaryCheckCode_iff (first + second)).2
  refine ⟨potential, ?_⟩
  rw [levelTwo_coboundary0_eq]
  exact hp
end QEC.Coding.BDL26LevelTwoDistance
