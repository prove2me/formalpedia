-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndromeRaw_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:19:32.053098+00:00
-- url     : https://prove2.me/submissions/22173e17-495b-4570-b885-f72d8022d1c5

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
theorem _root_.solution (S : OddScale) (n : Nat) :
    (lowerSyndromeRaw S n) ∈ LinearMap.range
      (tannerCoboundary1 (rxReplacementPresentation (state S n).presentation S)) :=
  ⟨(lowerErrorRaw S n),rfl⟩
end QEC.Coding.BDL26UniformHistoryObstruction
