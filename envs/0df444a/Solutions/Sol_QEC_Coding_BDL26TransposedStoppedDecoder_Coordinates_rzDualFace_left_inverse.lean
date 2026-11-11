-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDualFace_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:59:55.513715+00:00
-- url     : https://prove2.me/submissions/a7eba346-82c3-4452-9605-7e2d3be6a799

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement hiding Two
open BDL26RZLocalReplacement hiding Two
open BDL26RZMap1CoordinateBridge hiding Two
open BDL26RXDecoderAdapter
open MultiscaleDecoder (BDL26Field)
open scoped Classical BigOperators
namespace QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (f : RZFace P S) : (rzDualFace P S).symm (rzDualFace P S f) = f :=
  (rzDualFace P S).symm_apply_apply f
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
