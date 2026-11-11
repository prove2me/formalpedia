-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.lifted_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:34:52.680238+00:00
-- url     : https://prove2.me/submissions/81cbfda3-b280-4275-a7ac-e193706aab70

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap_commutes_coboundary0


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) (p : Word F (P1 S).X) :
    tannerCoboundary0 (P2 S) (rzMap0Coord (P1 S) S p) =
      map1Coord (P1 S) (rxState S baseState).admissible S
        (tannerCoboundary0 (P1 S) p) := by
  have h := LinearMap.congr_fun
    (rzMap_commutes_coboundary0 (P1 S) (rxState S baseState).admissible S) p
  change rzCoboundary0 (P1 S) (rxState S baseState).admissible S
      (rzMap0Coord (P1 S) S p) =
    map1Coord (P1 S) (rxState S baseState).admissible S
      (tannerCoboundary0 (P1 S) p) at h
  funext q
  exact congrFun h q
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
