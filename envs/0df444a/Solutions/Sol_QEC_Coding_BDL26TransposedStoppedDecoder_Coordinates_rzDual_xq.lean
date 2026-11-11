-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rzDual_xq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:13:03.879206+00:00
-- url     : https://prove2.me/submissions/b40122f5-5844-4d95-acff-44c4cd969a5e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_xq_of_face_equiv
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rzDualFace_X
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
    (R : TannerSquareCellularRegular P) (S : OddScale) (x : (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).X) (q : (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).Q) :
    (rxReplacementPresentation (transposePresentation P) S).xq (rzDualX P S x) (rzDualQ P S q) = (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)).xq x q := by
  apply xq_of_face_equiv (transposePresentation (rzReplacementPresentation P A.toTannerSquareAdmissible S)) (rxReplacementPresentation (transposePresentation P) S)
    (transposeTannerSquareAdmissibleV4
      (rzReplacementPresentation P A.toTannerSquareAdmissible S)
      (rzReplacementAdmissibleV4 P A R S)).toTannerSquareAdmissible
    (rxReplacementAdmissibleV4 (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A) (transposeTannerSquareCellularRegular P R) S).toTannerSquareAdmissible (rzDualX P S) (rzDualQ P S) (rzDualFace P S)
  · exact rzDualFace_X P A.toTannerSquareAdmissible S
  · exact rzDualFace_Q P A.toTannerSquareAdmissible S
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
