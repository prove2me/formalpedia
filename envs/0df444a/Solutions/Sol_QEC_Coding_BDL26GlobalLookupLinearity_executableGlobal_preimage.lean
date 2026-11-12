-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.executableGlobal_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:43:57.007591+00:00
-- url     : https://prove2.me/submissions/53e0b991-4e70-4d11-bf30-b72284ad8b71

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
    executableSyndrome S (executableGlobal S (executableSyndrome S a))=
      executableSyndrome S a := global_preimage (executableLinear S) _ ⟨a,rfl⟩
end QEC.Coding.BDL26GlobalLookupLinearity
