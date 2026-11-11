-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDual_coboundary0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:20:38.824852+00:00
-- url     : https://prove2.me/submissions/f0163202-3179-464d-98e3-6ad93d47c9b7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_coboundary0_transport
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDual_xq

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
    (w : Word BDL26Field (transposePresentation (rxReplacementPresentation P S)).X) :
    tannerCoboundary0 (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S) (wordEquiv (rxDualX P S) w) =
      wordEquiv (rxDualQ P S) (tannerCoboundary0 (transposePresentation (rxReplacementPresentation P S)) w) := by
  funext z
  obtain ⟨z,rfl⟩ := (rxDualQ P S).surjective z
  change _ = tannerCoboundary0 (transposePresentation (rxReplacementPresentation P S)) w z
  exact
    coboundary0_transport (transposePresentation (rxReplacementPresentation P S)) (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S)
      (rxDualX P S) (rxDualQ P S) (rxDual_xq P A R S) w z
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
