-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.executableDecode_of_local_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:49:13.779768+00:00
-- url     : https://prove2.me/submissions/16b9962b-2e9f-495a-a247-257339867b61

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_lookup_eq_global_of_local_none

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
namespace QEC.Coding.BDL26GlobalLookupLinearity
theorem _root_.solution (S : OddScale) (s : Word Bit (ExecutableZ S))
    (h : search (fun e => executableLocal S e && decide (executableSyndrome S e=s))
      (allWords (ExecutableQ S))=none) :
    executableDecode S s=executableGlobal S s :=
  lookup_eq_global_of_local_none (executableLinear S) (executableLocal S) s h
end QEC.Coding.BDL26GlobalLookupLinearity
