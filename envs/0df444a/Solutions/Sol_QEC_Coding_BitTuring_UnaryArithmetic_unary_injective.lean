-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.unary_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:04:35.812132+00:00
-- url     : https://prove2.me/submissions/50d7aada-b4b4-45a0-b9d2-1be267104d93

import Definitions.Def_QEC_Coding_BitTuring_Composition
import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic
theorem _root_.solution : Function.Injective unary := by
  intro a b h
  simpa only [unary_length] using congrArg List.length h
end QEC.Coding.BitTuring.UnaryArithmetic
