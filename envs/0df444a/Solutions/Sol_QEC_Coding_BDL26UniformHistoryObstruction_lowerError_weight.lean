-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.lowerError_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:20:59.064474+00:00
-- url     : https://prove2.me/submissions/99baa3b9-8507-4c06-9209-71794e6b5b28

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerErrorRaw_weight
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

section
namespace QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
private theorem weight_transport (P U : TannerSquarePresentation) (h : P = U)
    (e : Word BDL26Field U.Q) :
    HammingWeight (Eq.mpr
      (congrArg (fun T : TannerSquarePresentation => Word BDL26Field T.Q) h) e) =
      HammingWeight e := by
  cases h
  rfl
end QEC.Coding.BDL26UniformHistoryObstruction
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat) :
    HammingWeight (lowerError S j) = 1 := by
  have h := weight_transport _ _
    (congrArg ConstructionState.presentation (state_rx S (2 * j + 2) (by omega)))
    (lowerErrorRaw S (2 * j + 2))
  exact h.trans (lowerErrorRaw_weight S (2 * j + 2))
end QEC.Coding.BDL26UniformHistoryObstruction
