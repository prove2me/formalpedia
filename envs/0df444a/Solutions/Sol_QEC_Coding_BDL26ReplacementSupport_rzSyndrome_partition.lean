-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementSupport.rzSyndrome_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:50:19.234907+00:00
-- url     : https://prove2.me/submissions/a501186a-f6b7-4916-b8c2-c5d83669d8bb

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
    (word : Word Field (RZZ P S)) :
    (∑ z : P.Z, fiberPart (rzSyndromeOwner P S) z word) = word := by
  classical
  exact sum_fiberPart _ _
end QEC.Coding.BDL26ReplacementSupport
