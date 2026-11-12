-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementSupport.rzCzH2Coordinate_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:51:31.207216+00:00
-- url     : https://prove2.me/submissions/3eb975a2-8c1b-4d09-9d34-3f3f8444f2b6

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
    (syndrome : Word Field (ZDoubleCylinderVertex P z S)) :
    HammingWeight (fun _ : Unit => rzCzH2Coordinate P z S
      ((LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2)).mkQ syndrome)) ≤
        HammingWeight syndrome := by
  have heq : (fun _ : Unit => rzCzH2Coordinate P z S
      ((LinearMap.range (wordLinearMapTranspose (rzCz P z S).boundary2)).mkQ syndrome)) =
      parityBit syndrome := by
    funext u
    exact rzCzH2Coordinate_mk P z S syndrome
  rw [heq]
  exact parityBit_weight_le syndrome
end QEC.Coding.BDL26ReplacementSupport
