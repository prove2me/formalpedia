-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.residual_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:24:31.664238+00:00
-- url     : https://prove2.me/submissions/15764b27-42ef-404b-9e67-13b65dc2005e

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
theorem _root_.solution (L : Word Bit A →ₗ[Bit] Word Bit B)
    (a b : Word Bit A) :
    (a+b)+G L (L (a+b))=(a+G L (L a))+(b+G L (L b)) := by
  rw [map_add,global_add_words]
  abel
end QEC.Coding.BDL26GlobalLookupLinearity
