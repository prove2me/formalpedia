-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.unary_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:03:59.867619+00:00
-- url     : https://prove2.me/submissions/c46bde11-ee67-4a22-8643-80c504d3b977

import Definitions.Def_QEC_Coding_BitTuring_Composition
import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic
theorem _root_.solution (n : ℕ) : (unary n).length = n := by simp [unary]
end QEC.Coding.BitTuring.UnaryArithmetic
