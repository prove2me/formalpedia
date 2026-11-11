-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDualFace_right_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:00:06.008593+00:00
-- url     : https://prove2.me/submissions/09a69e6d-16a8-4026-8a99-b5e22158624f

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
    (f : RXFace (transposePresentation P) S) :
    rzDualFace P S ((rzDualFace P S).symm f) = f :=
  (rzDualFace P S).apply_symm_apply f
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
