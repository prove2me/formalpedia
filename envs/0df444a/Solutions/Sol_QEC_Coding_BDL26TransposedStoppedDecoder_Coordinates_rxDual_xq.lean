-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.rxDual_xq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:14:09.32669+00:00
-- url     : https://prove2.me/submissions/27e0678c-11d1-4436-8f1c-ba0e227bbb7c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_xq_of_face_equiv
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_rxDualFace_X
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
    (R : TannerSquareCellularRegular P) (S : OddScale) (x : (transposePresentation (rxReplacementPresentation P S)).X) (q : (transposePresentation (rxReplacementPresentation P S)).Q) :
    (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S).xq (rxDualX P S x) (rxDualQ P S q) = (transposePresentation (rxReplacementPresentation P S)).xq x q := by
  apply xq_of_face_equiv (transposePresentation (rxReplacementPresentation P S)) (rzReplacementPresentation (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S)
    (transposeTannerSquareAdmissibleV4 (rxReplacementPresentation P S)
      (rxReplacementAdmissibleV4 P A R S)).toTannerSquareAdmissible
    (rzReplacementAdmissibleV4 (transposePresentation P)
      (transposeTannerSquareAdmissibleV4 P A) (transposeTannerSquareCellularRegular P R) S).toTannerSquareAdmissible (rxDualX P S) (rxDualQ P S) (rxDualFace P S)
  · exact rxDualFace_X P S
  · exact rxDualFace_Q P (transposeTannerSquareAdmissibleV4 P A).toTannerSquareAdmissible S
end QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
