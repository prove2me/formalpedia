-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.lower_input_raw_z_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:19:05.09202+00:00
-- url     : https://prove2.me/submissions/9e2fed94-6758-408e-9085-48da8d1a8bd6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_extendedRadialGauge_supported


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
    (z : (state S n).presentation.Z) (b : Fin 2) :
    rxCoboundary1 (state S n).presentation S (lowerErrorRaw S n) (Sum.inr (z,b)) = 0 :=
  extendedRadialGauge_supported (state S n).presentation
    (state S n).admissible.toTannerSquareAdmissible S (retainedX S n) 0 (retainedAlpha S n)
    (Sum.inr (z,b)) (by intro h; cases h)
end QEC.Coding.BDL26UniformRXTail
