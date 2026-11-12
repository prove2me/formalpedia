-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_xSyndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:44:35.990205+00:00
-- url     : https://prove2.me/submissions/e697c167-5759-49ad-a70c-3d48dcfaeb3e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualBaseDecode_syndrome
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dual_coboundary1_xSyndrome

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26LevelTwoCode BDL26LevelTwoDecoder BDL26ReplacementSupport
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge MultiscaleDecoder Coordinates
open scoped Classical
namespace QEC.Coding.BDL26TransposedStoppedDecoder
theorem _root_.solution (S : OddScale)
    (sigma : Word BDL26Field (BDL26CSSHamiltonian.XLabel S 2))
    (h : sigma ∈ LinearMap.range (BDL26CSSHamiltonian.xSyndrome S 2)) :
    BDL26CSSHamiltonian.xSyndrome S 2 (dualBaseDecode S sigma) = sigma := by
  rw [← dual_coboundary1_xSyndrome] at h ⊢
  exact dualBaseDecode_syndrome S sigma h
end QEC.Coding.BDL26TransposedStoppedDecoder
