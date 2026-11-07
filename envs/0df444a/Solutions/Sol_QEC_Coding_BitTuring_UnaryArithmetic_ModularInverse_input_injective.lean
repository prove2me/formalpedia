-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ModularInverse.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:31:17.461201+00:00
-- url     : https://prove2.me/submissions/d1973876-fe6b-4004-8cec-89df4a34b6c7

import Definitions.Def_QEC_Coding_BitTuring_UnaryProductSearch
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldInverse
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_pairInput_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularInverse
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularInverse
theorem _root_.solution : Function.Injective input := by
  intro x y h
  exact Subtype.ext (pairInput_injective h)
end QEC.Coding.BitTuring.UnaryArithmetic.ModularInverse
