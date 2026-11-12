-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.upperError_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:20:33.332963+00:00
-- url     : https://prove2.me/submissions/fac0365c-4f83-48e5-9611-89cf02396985

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks
open BDL26OwnerParentObstruction BDL26ReplacementSupport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat) :
    (indexedFamily S (2 * j + 4)).coboundary1 (TopIndex (2 * j + 4))
      (upperError S j) = (upperSyndrome S j).val :=
  LinearMap.congr_fun
    (((indexedDecoderData S (2 * j + 4)).selectedMap
      ⟨2 * j + 3, by omega⟩).commutes_coboundary1) (lowerError S j)
end QEC.Coding.BDL26UniformHistoryObstruction
