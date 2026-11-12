-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerParentObstruction.evidenceLowerSyndrome_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:13:58.238342+00:00
-- url     : https://prove2.me/submissions/2988ffa8-a96b-4f5b-8c41-99546d9c1ae6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction

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
    evidenceLowerSyndrome ∈ LinearMap.range
      (tannerCoboundary1 (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)) :=
  ⟨evidenceCorrection,rfl⟩
end QEC.Coding.BDL26OwnerParentObstruction
