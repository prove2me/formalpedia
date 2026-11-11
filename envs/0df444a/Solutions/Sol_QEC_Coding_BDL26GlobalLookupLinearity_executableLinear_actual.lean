-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.executableLinear_actual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:02:56.025573+00:00
-- url     : https://prove2.me/submissions/31462fa0-ec11-4faf-9275-4f662ac03ad9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_executableSyndrome_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
namespace QEC.Coding.BDL26GlobalLookupLinearity
theorem _root_.solution (S : OddScale)
    (a : Word Bit (levelTwoPresentation S).Q) :
    executableLinear S (toExecutableError S a)=
      toExecutableSyndrome S (tannerCoboundary1 (levelTwoPresentation S) a) :=
  executableSyndrome_eq S a
end QEC.Coding.BDL26GlobalLookupLinearity
