-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.lower_input_other_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:29:07.508846+00:00
-- url     : https://prove2.me/submissions/24683cdd-23f4-4f8c-8639-acaf285245ed

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerSyndromeRaw_owner


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26DecodingGraph BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26IndexedDecoder
open BDL26UniformHistoryObstruction BDL26OwnerParentObstruction
open BDL26RXLocalReplacement BDL26XLocalRadialParity
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (n : Nat)
    (z : RX2 (state S n).presentation S)
    (hz : rxSyndromeOwner (state S n).presentation S z ≠ .x (retainedX S n)) :
    lowerSyndromeRaw S n z = 0 := by
  by_contra h
  exact hz (lowerSyndromeRaw_owner S n z h)
end QEC.Coding.BDL26UniformRXTail
