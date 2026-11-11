-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.chain_boundary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:47:39.487497+00:00
-- url     : https://prove2.me/submissions/9d136db1-faad-4ba3-b20a-222945e43a03

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) (w : Error S) :
    w ∈ (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier ↔
      w ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by
  constructor
  · intro hw
    obtain ⟨p,hp⟩ := ((levelTwoChainComplex S).mem_firstCoboundaryCheckCode_iff w).1 hw
    refine ⟨p,?_⟩
    rw [levelTwo_coboundary0_eq] at hp
    exact hp
  · rintro ⟨p,hp⟩
    apply ((levelTwoChainComplex S).mem_firstCoboundaryCheckCode_iff w).2
    refine ⟨p,?_⟩
    rw [levelTwo_coboundary0_eq]
    exact hp
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
