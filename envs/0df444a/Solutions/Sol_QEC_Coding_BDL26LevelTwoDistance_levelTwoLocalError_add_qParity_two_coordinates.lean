-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_add_qParity_two_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:32:40.633803+00:00
-- url     : https://prove2.me/submissions/1d65065a-e022-475f-85f5-9a0c76d11e66

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_add_qParity_support
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_qCoordinateOfOwner_of_eq

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
    (defaultQ : (levelOnePresentation S).Q)
    (first second : Word Field (levelTwoPresentation S).Q)
    (hfirst : levelTwoLocalError S first) (hsecond : levelTwoLocalError S second) :
    ∃ a b : (levelOnePresentation S).Q,
      ∀ q, rzQParity (levelOnePresentation S) S (first + second) q ≠ 0 → q = a ∨ q = b := by
  obtain ⟨a, b, hab⟩ := levelTwoLocalError_add_qParity_support S first second hfirst hsecond
  refine ⟨qCoordinateOfOwner _ defaultQ a, qCoordinateOfOwner _ defaultQ b, ?_⟩
  intro q hq
  rcases hab q hq with ha | hb
  · exact Or.inl (qCoordinateOfOwner_of_eq _ defaultQ q a ha)
  · exact Or.inr (qCoordinateOfOwner_of_eq _ defaultQ q b hb)
end QEC.Coding.BDL26LevelTwoDistance
