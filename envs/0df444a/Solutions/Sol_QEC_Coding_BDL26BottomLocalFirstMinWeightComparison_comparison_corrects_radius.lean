-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:27:01.527743+00:00
-- url     : https://prove2.me/submissions/e77df30d-aeab-49d4-b1df-267f5b551436

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_rightInverse
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_local_or_weight
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_radius_error_local_preimage
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_radius_error_light_preimage

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) (r : Nat)
    (large : 2*r+2 ≤ S.half) (e : Error S) (small : HammingWeight e ≤ r) :
    e+ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
      LinearMap.range (tannerCoboundary0 (P2 S)) := by
  have same := comparison_rightInverse S (tannerCoboundary1 (P2 S) e) ⟨e,rfl⟩
  rcases comparison_local_or_weight S e with hlocal | light
  · exact radius_error_local_preimage S r large e _ small hlocal same
  · exact radius_error_light_preimage S r large e _ small light same
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
