-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDual_coboundary0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:18:41.021779+00:00
-- url     : https://prove2.me/submissions/18cd456d-ddf9-474a-8a69-94bf9c52a7dd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_coboundary0_transport
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDual_xq

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
    (w : Word BDL26Field (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).X) :
    tannerCoboundary0 (rxReplacementPresentation (transposePresentation P) S) (wordEquiv (rzDualX P S) w) =
      wordEquiv (rzDualQ P S) (tannerCoboundary0 (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) w) := by
  funext z
  obtain ⟨z,rfl⟩ := (rzDualQ P S).surjective z
  change _ = tannerCoboundary0 (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) w z
  exact
    coboundary0_transport (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) (rxReplacementPresentation (transposePresentation P) S)
      (rzDualX P S) (rzDualQ P S) (rzDual_xq P A R S) w z
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
