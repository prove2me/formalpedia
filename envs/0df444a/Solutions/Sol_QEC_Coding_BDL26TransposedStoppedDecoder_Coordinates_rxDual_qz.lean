-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDual_qz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:13:00.644774+00:00
-- url     : https://prove2.me/submissions/b11e6660-b3e1-4350-bb5e-86385d677837

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_qz_of_face_equiv
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDualFace_Z
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDualFace_Q

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
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) (q : (transposePresentation (rxReplacementPresentation P S)).Q) (z : (transposePresentation (rxReplacementPresentation P S)).Z) :
    (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S).qz (rxDualQ P S q) (rxDualZ P S z) = (transposePresentation (rxReplacementPresentation P S)).qz q z := by
  apply qz_of_face_equiv (transposePresentation (rxReplacementPresentation P S)) (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S)
    (transposeTannerSquareAdmissibleV4 (rxReplacementPresentation P S)
      (rxReplacementAdmissibleV4 P A R S)).toTannerSquareAdmissible
    (rzReplacementAdmissibleV4 (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A) (transposeTannerSquareCellularRegular P R) S).toTannerSquareAdmissible (rxDualQ P S) (rxDualZ P S) (rxDualFace P S)
  · exact rxDualFace_Z P (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S
  · exact rxDualFace_Q P (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
