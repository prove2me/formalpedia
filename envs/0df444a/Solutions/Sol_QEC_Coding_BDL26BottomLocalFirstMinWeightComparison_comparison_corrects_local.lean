-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.comparison_corrects_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:06:05.46722+00:00
-- url     : https://prove2.me/submissions/2a47c937-28f9-4b43-924c-3e8e44b3dc86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_comparison_agrees_of_local_preimage
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_chain_boundary_iff
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_decode_corrects_local


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) (e : Error S)
    (he : levelTwoLocalError S e) :
    e + ownerFirstMinWeightFallback S (tannerCoboundary1 (P2 S) e) ∈
      LinearMap.range (tannerCoboundary0 (P2 S)) := by
  rw [comparison_agrees_of_local_preimage S _ e he rfl]
  exact (chain_boundary_iff S _).1 (decode_corrects_local S e he)
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
