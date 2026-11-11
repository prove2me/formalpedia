-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_weight_seven_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:25:18.331684+00:00
-- url     : https://prove2.me/submissions/7eff70ba-bbd5-452a-9310-e2c2c26d727f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_chain_boundary_iff
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_corrects_weight_seven

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) (large : 16 ≤ S.half)
    (e : Error S) (small : HammingWeight e ≤ 7) :
    e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
      (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier :=
  (chain_boundary_iff S _).2 (comparison_corrects_weight_seven S large e small)
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
