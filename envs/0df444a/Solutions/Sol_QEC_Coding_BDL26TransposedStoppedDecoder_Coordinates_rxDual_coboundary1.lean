-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDual_coboundary1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:19:32.735738+00:00
-- url     : https://prove2.me/submissions/8eda5d7e-c0fc-49c8-a28f-81b7b499980e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_coboundary1_transport
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDual_qz

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
    (w : Word BDL26Field (transposePresentation (rxReplacementPresentation P S)).Q) :
    tannerCoboundary1 (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S) (wordEquiv (rxDualQ P S) w) =
      wordEquiv (rxDualZ P S) (tannerCoboundary1 (transposePresentation (rxReplacementPresentation P S)) w) := by
  funext z
  obtain ⟨z,rfl⟩ := (rxDualZ P S).surjective z
  change _ = tannerCoboundary1 (transposePresentation (rxReplacementPresentation P S)) w z
  exact
    coboundary1_transport (transposePresentation (rxReplacementPresentation P S)) (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S)
      (rxDualQ P S) (rxDualZ P S) (rxDual_qz P A R S) w z
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
