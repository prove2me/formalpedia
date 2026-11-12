-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.lower_syndrome_z_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:32:11.033308+00:00
-- url     : https://prove2.me/submissions/12eba0ff-d7f7-4236-b537-dad82dc35e33

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxTransport_boundary_z_zero
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_input_raw_z_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 2)).presentation.Z) (b : Fin 2) :
    (lowerSyndrome S j).val ((tailData S j).induced.zPairEquiv (z,b)).val = 0 := by
  exact rxTransport_boundary_z_zero S (2*j+4) (tailIndex j) (tailIndex_even j)
    (lowerErrorRaw S (2*j+2)) (lower_input_raw_z_zero S (2*j+2)) z b
end QEC.Coding.BDL26UniformRXTail
