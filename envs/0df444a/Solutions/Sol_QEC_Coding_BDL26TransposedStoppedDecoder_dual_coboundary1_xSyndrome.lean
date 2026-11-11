-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.dual_coboundary1_xSyndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:42:07.844734+00:00
-- url     : https://prove2.me/submissions/84878f9d-82b8-4223-9c0a-a57d8c2f360a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_xSyndrome_transposed
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26LevelTwoCode BDL26LevelTwoDecoder BDL26ReplacementSupport
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge MultiscaleDecoder Coordinates
open scoped Classical
namespace QEC.Coding.BDL26TransposedStoppedDecoder
theorem _root_.solution (S : OddScale) (n : Nat) :
    tannerCoboundary1 (dualPresentation S n) = BDL26CSSHamiltonian.xSyndrome S n :=
  (BDL26CSSHamiltonian.xSyndrome_transposed S n).symm
end QEC.Coding.BDL26TransposedStoppedDecoder
