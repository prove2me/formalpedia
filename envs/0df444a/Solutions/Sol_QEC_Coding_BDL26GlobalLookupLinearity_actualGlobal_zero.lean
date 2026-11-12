-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.actualGlobal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:44:36.574836+00:00
-- url     : https://prove2.me/submissions/1bf291ac-4412-4af7-9f8b-15e3c25c4770

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_executableGlobal_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_toActualError_zero
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_toExecutableSyndrome_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
namespace QEC.Coding.BDL26GlobalLookupLinearity
theorem _root_.solution (S : OddScale) : actualGlobal S 0=0 := by
  unfold actualGlobal
  rw [toExecutableSyndrome_zero,executableGlobal_zero,toActualError_zero]
end QEC.Coding.BDL26GlobalLookupLinearity
