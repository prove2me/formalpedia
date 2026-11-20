-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparisonBaseAdapter_correctsLocalErrors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:10:47.044863+00:00
-- url     : https://prove2.me/submissions/8c3a85df-ceb3-458e-bd00-27ebda6e4d3b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_chain_boundary_iff
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_corrects_local

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) :
    (comparisonBaseAdapter S).CorrectsLocalErrors (levelTwoLocalComplex S) := by
  intro input hlocal
  have he : levelTwoLocalError S input.error := hlocal
  let e : Error S := input.error
  change e+ownerFirstMinWeightFallback S ((decoderFamily S).coboundary1
      (MultiscaleDecoder.levelTwoIndex (show 2 ≤ 2 from le_rfl)) e) ∈
    (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier
  rw [decoderFamily_coboundary1]
  exact (chain_boundary_iff S _).2 (comparison_corrects_local S e he)
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
