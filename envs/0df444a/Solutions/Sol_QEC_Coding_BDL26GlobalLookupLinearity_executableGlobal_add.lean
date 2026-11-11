-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.executableGlobal_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:44:37.559852+00:00
-- url     : https://prove2.me/submissions/5619efba-9b0d-4af2-b268-edf457332307

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
namespace QEC.Coding.BDL26GlobalLookupLinearity
theorem _root_.solution (S : OddScale) (a b : Word Bit (ExecutableQ S)) :
    executableGlobal S (executableSyndrome S a+executableSyndrome S b)=
      executableGlobal S (executableSyndrome S a)+executableGlobal S (executableSyndrome S b) :=
  global_add_words (executableLinear S) a b
end QEC.Coding.BDL26GlobalLookupLinearity
