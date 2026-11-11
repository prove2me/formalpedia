-- Prove2me | solution 1 for QEC.Coding.BDL26TransposedStoppedDecoder.mem_dualBaseTable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:37:40.572262+00:00
-- url     : https://prove2.me/submissions/5a8e581b-ccaa-4dce-b1b5-eccc51614dbd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_mem_allWords


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26LevelTwoCode BDL26LevelTwoDecoder BDL26ReplacementSupport
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge MultiscaleDecoder Coordinates
open scoped Classical
namespace QEC.Coding.BDL26TransposedStoppedDecoder
theorem _root_.solution (S : OddScale) (e : Word BDL26Field (dualPresentation S 2).Q) :
    e ∈ dualBaseTable S := by
  apply List.mem_map.mpr
  exact ⟨toExecutableError S e,mem_allWords _ _,toActualError_toExecutableError S e⟩
end QEC.Coding.BDL26TransposedStoppedDecoder
