-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:44:08.70706+00:00
-- url     : https://prove2.me/submissions/5e98322b-903d-4e47-b025-af926193899a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_mem_dualBaseTable
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_lookup_local


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
    (e : Word BDL26Field (dualPresentation S 2).Q) (h : dualBaseLocal S e = true) :
    dualBaseLocal S (dualBaseDecode S (tannerCoboundary1 (dualPresentation S 2) e)) = true :=
  lookup_local _ _ _ _ _ ⟨e,mem_dualBaseTable S e,h,rfl⟩
end QEC.Coding.BDL26TransposedStoppedDecoder
