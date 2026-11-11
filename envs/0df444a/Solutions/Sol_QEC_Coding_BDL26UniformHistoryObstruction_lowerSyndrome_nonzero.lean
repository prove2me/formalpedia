-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.lowerSyndrome_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:36:04.979097+00:00
-- url     : https://prove2.me/submissions/cb82f7a5-ffa4-4e84-86ca-0d902f75bbb0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerSyndromeRaw_nonzero
section
namespace QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks
open BDL26OwnerParentObstruction BDL26ReplacementSupport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open MultiscaleDecoder
open scoped Classical
private theorem transported_syndrome_nonzero
    (P U : TannerSquarePresentation) (h : P = U)
    (e : Word BDL26Field U.Q) (he : tannerCoboundary1 U e ≠ 0) :
    tannerCoboundary1 P
      (Eq.mpr (congrArg (fun T : TannerSquarePresentation => Word BDL26Field T.Q) h) e) ≠ 0 := by
  cases h
  exact he
end QEC.Coding.BDL26UniformHistoryObstruction
end

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
    (lowerSyndrome S j).val ≠ 0 := by
  change (indexedFamily S (2 * j + 4)).coboundary1
    ⟨2 * j + 3, by omega⟩ (lowerError S j) ≠ 0
  rw [indexedFamily_coboundary1]
  exact transported_syndrome_nonzero _ _
    (congrArg ConstructionState.presentation (state_rx S (2 * j + 2) (by omega)))
    (lowerErrorRaw S (2 * j + 2)) (lowerSyndromeRaw_nonzero S (2 * j + 2))
end QEC.Coding.BDL26UniformHistoryObstruction
