-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementSupport.rzLocalParity_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:50:40.48943+00:00
-- url     : https://prove2.me/submissions/688515a1-3da3-490a-bf30-b3cea2ea4e81

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_parityBit_weight_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical
namespace QEC.Coding.BDL26ReplacementSupport
theorem _root_.solution
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (syndrome : Word Field (RZZ P S)) :
    HammingWeight (parityBit (fun vertex : ZDoubleCylinderVertex P z S =>
      syndrome ⟨z, vertex⟩)) ≤
      HammingWeight (fun vertex : ZDoubleCylinderVertex P z S => syndrome ⟨z, vertex⟩) :=
  parityBit_weight_le _
end QEC.Coding.BDL26ReplacementSupport
