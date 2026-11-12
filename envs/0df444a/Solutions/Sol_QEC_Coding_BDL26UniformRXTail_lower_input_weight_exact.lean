-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.lower_input_weight_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:30:03.663507+00:00
-- url     : https://prove2.me/submissions/bfe9ab4f-13d8-4e20-8e3c-5da11c19635a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_input_support
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_inputSpot_injective

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
theorem _root_.solution (S : OddScale) (n : Nat) :
    HammingWeight (lowerSyndromeRaw S n) = (incidentStarFaces S n).card := by
  rw [HammingWeight, lower_input_support,
    Finset.card_image_of_injective _ (inputSpot_injective S n)]
end QEC.Coding.BDL26UniformRXTail
