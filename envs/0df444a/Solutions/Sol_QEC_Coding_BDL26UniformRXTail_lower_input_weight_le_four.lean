-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.lower_input_weight_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:53:12.964083+00:00
-- url     : https://prove2.me/submissions/bf48b7e1-4f07-45af-9a5b-35ad2ac1e275

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_input_weight_valence
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence


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
theorem _root_.solution (S : OddScale) (n : Nat) :
    HammingWeight (lowerSyndromeRaw S n) ≤ 4 := by
  rw [lower_input_weight_valence]
  exact ((state_boundedValence S n).2.2 (selectedNeighbor S n).val).2.1
end QEC.Coding.BDL26UniformRXTail
