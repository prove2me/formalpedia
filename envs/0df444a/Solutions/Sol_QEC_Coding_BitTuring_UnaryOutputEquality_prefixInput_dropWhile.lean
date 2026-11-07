-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryOutputEquality.prefixInput_dropWhile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:06:26.119007+00:00
-- url     : https://prove2.me/submissions/2137522f-3285-4463-9884-9cc1885513b4

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryOutputEquality
open Turing StateTransition UnaryArithmetic
variable (A : Machine)
namespace QEC.Coding.BitTuring.UnaryOutputEquality
theorem _root_.solution (r : ℕ) (x : List Bool) :
    (prefixInput r x).dropWhile id=false::x := by
  induction r with
  | zero => simp [prefixInput,unary]
  | succ r ih => simpa [prefixInput,unary_succ] using ih
end QEC.Coding.BitTuring.UnaryOutputEquality
