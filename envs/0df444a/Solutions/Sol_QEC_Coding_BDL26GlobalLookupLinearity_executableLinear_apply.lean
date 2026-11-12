-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.executableLinear_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:43:41.3582+00:00
-- url     : https://prove2.me/submissions/d42e1437-4947-46e3-acfc-ba7853326d2d

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
theorem _root_.solution (S : OddScale) (a : Word Bit (ExecutableQ S)) :
    executableLinear S a=executableSyndrome S a := rfl
end QEC.Coding.BDL26GlobalLookupLinearity
