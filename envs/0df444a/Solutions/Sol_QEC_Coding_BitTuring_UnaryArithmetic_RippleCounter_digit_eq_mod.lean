-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digit_eq_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:29.021973+00:00
-- url     : https://prove2.me/submissions/0d936be2-0b29-4149-8958-6d604e0e633e

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounter
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter
theorem _root_.solution (q x:ℕ) (carry:Bool) (hx:x<q):digit q x carry=(candidate x carry)%q:=by
 have hy:=candidate_le q x carry hx
 by_cases he:candidate x carry=q
 · simp [digit,carried,he]
 · have hl:candidate x carry<q:=by omega
   have hc:carried q x carry=false:=by simp [carried,he]
   simp only [digit,hc,Bool.false_eq_true,↓reduceIte,Nat.mod_eq_of_lt hl]
end QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter
