-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDual_coboundary1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:19:21.211832+00:00
-- url     : https://prove2.me/submissions/a97a7b2a-ea13-4811-8969-1a181650ca75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_coboundary1_transport
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDual_qz

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
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Word BDL26Field (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).Q) :
    tannerCoboundary1 (rxReplacementPresentation (transposePresentation P) S) (wordEquiv (rzDualQ P S) w) =
      wordEquiv (rzDualZ P S) (tannerCoboundary1 (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) w) := by
  funext z
  obtain ⟨z,rfl⟩ := (rzDualZ P S).surjective z
  change _ = tannerCoboundary1 (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) w z
  exact
    coboundary1_transport (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) (rxReplacementPresentation (transposePresentation P) S)
      (rzDualQ P S) (rzDualZ P S) (rzDual_qz P A R S) w z
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
