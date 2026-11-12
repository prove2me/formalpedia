-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.lower_syndrome_weight_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:57:30.693883+00:00
-- url     : https://prove2.me/submissions/4be7bc92-e842-4fef-a390-271fc9ff3461

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_input_weight_le_four
section
namespace QEC.Coding.BDL26UniformRXTail
open BDL26DecodingGraph BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26IndexedDecoder
open BDL26UniformHistoryObstruction BDL26OwnerParentObstruction
open BDL26RXLocalReplacement BDL26XLocalRadialParity
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26BoundedValence
private theorem syndrome_weight_transport (P U : TannerSquarePresentation) (h : P = U)
    (e : Word BDL26Field U.Q) :
    HammingWeight (tannerCoboundary1 P (Eq.mpr
      (congrArg (fun T : TannerSquarePresentation => Word BDL26Field T.Q) h) e)) =
      HammingWeight (tannerCoboundary1 U e) := by
  cases h
  rfl
end QEC.Coding.BDL26UniformRXTail
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26DecodingGraph BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26IndexedDecoder
open BDL26UniformHistoryObstruction BDL26OwnerParentObstruction
open BDL26RXLocalReplacement BDL26XLocalRadialParity
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26BoundedValence
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (j : Nat) :
    HammingWeight (lowerSyndrome S j).val ≤ 4 := by
  change HammingWeight ((indexedFamily S (2 * j + 4)).coboundary1
    ⟨2 * j + 3, by omega⟩ (lowerError S j)) ≤ 4
  rw [indexedFamily_coboundary1]
  have h := syndrome_weight_transport _ _
    (congrArg ConstructionState.presentation (state_rx S (2 * j + 2) (by omega)))
    (lowerErrorRaw S (2 * j + 2))
  exact h.trans_le (lower_input_weight_le_four S (2 * j + 2))
end QEC.Coding.BDL26UniformRXTail
