-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:55:55.789246+00:00
-- url     : https://prove2.me/submissions/bc20a510-c9f6-4c71-9fb4-df8c5fbe79a0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_mem_dualBaseTable
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_lookup_syndrome


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
    (sigma : Word BDL26Field (dualPresentation S 2).Z)
    (h : sigma ∈ LinearMap.range (tannerCoboundary1 (dualPresentation S 2))) :
    tannerCoboundary1 (dualPresentation S 2) (dualBaseDecode S sigma) = sigma := by
  obtain ⟨e,he⟩ := h
  exact lookup_syndrome _ _ _ _ _ ⟨e,mem_dualBaseTable S e,he⟩
end QEC.Coding.BDL26TransposedStoppedDecoder
