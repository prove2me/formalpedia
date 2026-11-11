-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.rho_local_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:34:16.564238+00:00
-- url     : https://prove2.me/submissions/7aa2e92a-d119-447b-9c9c-822e2ad2c553

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_iff_owner
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_qCoordinateOfOwner_of_eq
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_zero_of_other_owner


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) (w : Error S)
    (hw : levelTwoLocalError S w) :
    ∃ a : (P1 S).Q, ∀ q, q ≠ a → rho S w q = 0 := by
  obtain ⟨owner,ho⟩ := (levelTwoLocalError_iff_owner S w).1 hw
  let a := qCoordinateOfOwner (P1 S) (levelOneQDefault S) owner
  refine ⟨a,?_⟩
  intro q hq
  apply rzQParity_zero_of_other_owner (P1 S) S w owner ho q
  intro h
  exact hq (qCoordinateOfOwner_of_eq (P1 S) (levelOneQDefault S) q owner h)
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
