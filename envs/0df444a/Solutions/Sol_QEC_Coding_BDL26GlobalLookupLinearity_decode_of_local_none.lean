-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.decode_of_local_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:55:47.061209+00:00
-- url     : https://prove2.me/submissions/d7e91056-881a-415a-af73-c0b4a7ddc6af

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_executableDecode_of_local_none

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
namespace QEC.Coding.BDL26GlobalLookupLinearity
theorem _root_.solution (S : OddScale) (s : Word Bit (levelTwoPresentation S).Z)
    (h : search (fun e => executableLocal S e &&
      decide (executableSyndrome S e=toExecutableSyndrome S s))
      (allWords (ExecutableQ S))=none) : decode S s=actualGlobal S s := by
  unfold decode actualGlobal
  rw [executableDecode_of_local_none S _ h]
end QEC.Coding.BDL26GlobalLookupLinearity
