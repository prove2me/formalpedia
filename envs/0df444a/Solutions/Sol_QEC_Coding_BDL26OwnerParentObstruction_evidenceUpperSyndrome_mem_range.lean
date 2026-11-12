-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerParentObstruction.evidenceUpperSyndrome_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:14:06.875894+00:00
-- url     : https://prove2.me/submissions/5c1d8eb2-c6f1-4379-8985-ff76cac5c97e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap_commutes_coboundary1


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerParentObstruction
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps MultiscaleDecoder
open scoped Classical
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open scoped BigOperators
namespace QEC.Coding.BDL26OwnerParentObstruction
theorem _root_.solution :
    evidenceUpperSyndrome ∈ LinearMap.range
      (rzCoboundary1 (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)
        (rxState scaleFive evidenceStateTwo).admissible scaleFive) := by
  refine ⟨map1Coord _ (rxState scaleFive evidenceStateTwo).admissible scaleFive evidenceCorrection,?_⟩
  exact congrArg (fun M => M evidenceCorrection)
    (rzMap_commutes_coboundary1 _ (rxState scaleFive evidenceStateTwo).admissible scaleFive)
end QEC.Coding.BDL26OwnerParentObstruction
