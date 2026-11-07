-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.SignedCoefficient.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:42.978823+00:00
-- url     : https://prove2.me/submissions/ddd9b8a3-8730-4b71-931e-3699d952e40f

import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularNegation
import Definitions.Def_QEC_Coding_BitTuring_UnarySignedCoefficient
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.SignedCoefficient
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.SignedCoefficient
theorem _root_.solution (c:ℤ) : Function.Injective (@input c) := by
  intro x y h
  have he:x.val.val=y.val.val := by
    change unary x.val.val=unary y.val.val at h
    simpa only [unary_length] using (congrArg (fun s:List Bool=>s.length) h)
  exact Subtype.ext (Subtype.ext he)
end QEC.Coding.BitTuring.UnaryArithmetic.SignedCoefficient
