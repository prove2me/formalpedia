-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.boolPairBits_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:56:26.83267+00:00
-- url     : https://prove2.me/submissions/d14fcaaa-1df2-4d84-b050-2f8e008d19fe

import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication
import Definitions.Def_QEC_Coding_BitTuring_UnaryComparison

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic
theorem _root_.solution : Function.Injective boolPairBits := by
  intro x y h
  have hx := List.cons.inj h
  exact Prod.ext hx.1 (List.cons.inj hx.2).1
end QEC.Coding.BitTuring.UnaryArithmetic
