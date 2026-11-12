-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementSupport.rzCorrection_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:49:55.692208+00:00
-- url     : https://prove2.me/submissions/7164cab4-a546-43c1-ae31-e796d279894a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_sum_fiberPart

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical
namespace QEC.Coding.BDL26ReplacementSupport
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RZQ P S)) :
    (∑ v : Vertex P, fiberPart (rzCorrectionOwner P S) v word) = word := by
  classical
  exact sum_fiberPart _ _
end QEC.Coding.BDL26ReplacementSupport
