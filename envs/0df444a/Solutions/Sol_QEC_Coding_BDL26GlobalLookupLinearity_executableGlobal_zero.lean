-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.executableGlobal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:44:31.981204+00:00
-- url     : https://prove2.me/submissions/2afffc02-e939-4444-b0ea-6a0180f705c6

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
theorem _root_.solution (S : OddScale) : executableGlobal S 0=0 :=
  global_zero (executableLinear S)
end QEC.Coding.BDL26GlobalLookupLinearity
