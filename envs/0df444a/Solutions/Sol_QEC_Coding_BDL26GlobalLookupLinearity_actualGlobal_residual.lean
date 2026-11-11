-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.actualGlobal_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:52:40.353168+00:00
-- url     : https://prove2.me/submissions/22c5afad-63d5-456a-8bad-34a48ed88daa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_actualGlobal_preimage

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
namespace QEC.Coding.BDL26GlobalLookupLinearity
theorem _root_.solution (S : OddScale) (a : Word Bit (levelTwoPresentation S).Q) :
    tannerCoboundary1 (levelTwoPresentation S)
      (a+actualGlobal S (tannerCoboundary1 (levelTwoPresentation S) a))=0 := by
  rw [map_add,actualGlobal_preimage]
  exact word_add_self (tannerCoboundary1 (levelTwoPresentation S) a)
end QEC.Coding.BDL26GlobalLookupLinearity
