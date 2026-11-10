-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_add_qParity_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:28:47.152192+00:00
-- url     : https://prove2.me/submissions/88507530-a75b-487d-bf82-4ecc5f972ff8

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_iff_owner
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_add_owner_support

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
    (hfirst : levelTwoLocalError S first) (hsecond : levelTwoLocalError S second) :
    ∃ firstOwner secondOwner : Vertex (levelOnePresentation S),
      ∀ q, rzQParity (levelOnePresentation S) S (first + second) q ≠ 0 →
        Vertex.q q = firstOwner ∨ Vertex.q q = secondOwner := by
  classical
  obtain ⟨a, ha⟩ := (levelTwoLocalError_iff_owner S first).1 hfirst
  obtain ⟨b, hb⟩ := (levelTwoLocalError_iff_owner S second).1 hsecond
  exact ⟨a, b, rzQParity_add_owner_support (levelOnePresentation S) S first second a b ha hb⟩
end QEC.Coding.BDL26LevelTwoDistance
