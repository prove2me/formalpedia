-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop.unaryInput_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:49.321592+00:00
-- url     : https://prove2.me/submissions/289cd1d5-0381-4dcf-a200-ecc4c50b4b24

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTrial
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryPrimality
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop
theorem _root_.solution : Function.Injective unaryInput := by
  intro x y h
  exact Subtype.ext (unary_injective h)
end QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop
