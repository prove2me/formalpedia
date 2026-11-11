-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:01:40.196448+00:00
-- url     : https://prove2.me/submissions/9ef40e57-7b65-40d9-9653-91eca62b136c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_agrees_of_local_preimage
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_decode_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_executableLocal_iff
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_executableLocal_zero
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) : ownerFirstMinWeightFallback S 0 = 0 := by
  have hlocal : levelTwoLocalError S (0 : Error S) := by
    apply (executableLocal_iff S _).1
    have transport_zero : toExecutableError S (0 : Error S) = 0 := by
      funext q
      rfl
    rw [transport_zero]
    exact executableLocal_zero S
  have h := comparison_agrees_of_local_preimage S 0 0 hlocal (map_zero _)
  exact h.trans (decode_zero S)
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
