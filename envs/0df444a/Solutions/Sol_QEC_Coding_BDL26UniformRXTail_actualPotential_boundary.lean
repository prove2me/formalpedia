-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actualPotential_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:30:19.702384+00:00
-- url     : https://prove2.me/submissions/a8b1f5af-8094-47cc-ad73-8358cca56229

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (j : Nat)
    (x : (state S (2*j+2)).presentation.X) :
    (tailData S j).contract.rx_local_complexes.cxDelta0 x (actualPotential S j x) =
      restrictWordLinear ((rxLx S (2*j+4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
        (errorAfterX S j) := Classical.choose_spec (actualPotential_exists S j x)
end QEC.Coding.BDL26UniformRXTail
