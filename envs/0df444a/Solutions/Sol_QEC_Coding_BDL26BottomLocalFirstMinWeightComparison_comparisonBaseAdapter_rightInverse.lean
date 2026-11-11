-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparisonBaseAdapter_rightInverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:17:59.797974+00:00
-- url     : https://prove2.me/submissions/7f1d1947-500d-48d6-8ce5-cab0ef50fc79

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_rightInverse

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
    (comparisonBaseAdapter S).IsRightInverse := by
  intro sigma
  change (decoderFamily S).coboundary1
    (MultiscaleDecoder.levelTwoIndex (show 2 ≤ 2 from le_rfl))
    (ownerFirstMinWeightFallback S sigma.val) = sigma.val
  rw [decoderFamily_coboundary1]
  apply comparison_rightInverse
  have hsigma : sigma.val ∈ LinearMap.range
      ((decoderFamily S).coboundary1
        (MultiscaleDecoder.levelTwoIndex (show 2 ≤ 2 from le_rfl))) := sigma.property
  rw [decoderFamily_coboundary1] at hsigma
  exact hsigma
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
