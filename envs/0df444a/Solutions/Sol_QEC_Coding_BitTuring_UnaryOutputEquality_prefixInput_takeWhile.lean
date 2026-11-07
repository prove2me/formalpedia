-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryOutputEquality.prefixInput_takeWhile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:06:08.692053+00:00
-- url     : https://prove2.me/submissions/cbc4b724-a158-45cf-826c-34f0b5de69e1

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryOutputEquality
open Turing StateTransition UnaryArithmetic
variable (A : Machine)
namespace QEC.Coding.BitTuring.UnaryOutputEquality
theorem _root_.solution (r : ℕ) (x : List Bool) :
    (prefixInput r x).takeWhile id=unary r := by
  induction r with
  | zero => simp [prefixInput,unary]
  | succ r ih => simpa [prefixInput,unary_succ] using congrArg (List.cons true) ih
end QEC.Coding.BitTuring.UnaryOutputEquality
