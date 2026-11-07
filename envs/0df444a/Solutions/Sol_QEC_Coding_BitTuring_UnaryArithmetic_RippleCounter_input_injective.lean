-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:28.237715+00:00
-- url     : https://prove2.me/submissions/b91b687c-56c1-4e85-baaa-ea95e6068c11

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixListQuery
import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrefixProjection_stream_suffix_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter
theorem _root_.solution (n:ℕ):Function.Injective (input n):=by
 intro x y h
 have he:=PrefixProjection.stream_suffix_injective (x.1.val.1::x.1.val.2) (y.1.val.1::y.1.val.2) x.2 y.2
  (by simp only [List.length_cons];rw [x.1.property.2.1,y.1.property.2.1]) h
 have hh:=List.cons.inj he.1
 exact Prod.ext (Subtype.ext (Prod.ext hh.1 hh.2)) he.2
end QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter
