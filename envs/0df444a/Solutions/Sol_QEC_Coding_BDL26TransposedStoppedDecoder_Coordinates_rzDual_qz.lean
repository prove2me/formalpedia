-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDual_qz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:13:10.502088+00:00
-- url     : https://prove2.me/submissions/4cd70d9d-7e02-48a4-adff-59bdacb5b14e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_qz_of_face_equiv
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDualFace_Z
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDualFace_Q

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
    (R : TannerSquareCellularRegular P) (S : OddScale) (q : (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).Q) (z : (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).Z) :
    (rxReplacementPresentation (transposePresentation P) S).qz (rzDualQ P S q) (rzDualZ P S z) = (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).qz q z := by
  apply qz_of_face_equiv (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) (rxReplacementPresentation (transposePresentation P) S)
    (transposeTannerSquareAdmissibleV4
      (rzReplacementPresentation P A.toTannerSquareAdmissible S)
      (rzReplacementAdmissibleV4 P A R S)).toTannerSquareAdmissible
    (rxReplacementAdmissibleV4 (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A) (transposeTannerSquareCellularRegular P R) S).toTannerSquareAdmissible (rzDualQ P S) (rzDualZ P S) (rzDualFace P S)
  · exact rzDualFace_Z P S
  · exact rzDualFace_Q P A.toTannerSquareAdmissible S
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
