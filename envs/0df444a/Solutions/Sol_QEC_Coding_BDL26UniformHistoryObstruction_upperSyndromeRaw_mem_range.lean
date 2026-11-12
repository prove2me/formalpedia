-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.upperSyndromeRaw_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:19:50.638896+00:00
-- url     : https://prove2.me/submissions/ef72e413-3e14-45fd-ad7b-0cc756eb815a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap_commutes_coboundary1


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
    (upperSyndromeRaw S n) ∈ LinearMap.range
      (rzCoboundary1 (rxReplacementPresentation (state S n).presentation S)
        (rxState S (state S n)).admissible S) := by
  refine ⟨map1Coord _ (rxState S (state S n)).admissible S (lowerErrorRaw S n),?_⟩
  exact congrArg (fun M => M (lowerErrorRaw S n))
    (rzMap_commutes_coboundary1 _ (rxState S (state S n)).admissible S)
end QEC.Coding.BDL26UniformHistoryObstruction
