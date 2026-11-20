-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.ownerFirstMinWeightFallback_contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:29:03.122219+00:00
-- url     : https://prove2.me/submissions/518bd57c-664f-4169-890d-d70623c3ba8b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_zero
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_corrects_weight_seven_code
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparisonBaseAdapter_rightInverse
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparisonBaseAdapter_correctsLocalErrors

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) (large : 16 ≤ S.half) :
    ownerFirstMinWeightFallback S 0 = 0 ∧
    (comparisonBaseAdapter S).IsRightInverse ∧
    (comparisonBaseAdapter S).CorrectsLocalErrors (levelTwoLocalComplex S) ∧
    ∀ e : Error S, HammingWeight e ≤ 7 →
      e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
        (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by
  exact ⟨comparison_zero S,comparisonBaseAdapter_rightInverse S,
    comparisonBaseAdapter_correctsLocalErrors S,comparison_corrects_weight_seven_code S large⟩
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
