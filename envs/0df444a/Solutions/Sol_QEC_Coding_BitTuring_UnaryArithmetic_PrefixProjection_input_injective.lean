-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:15:06.605193+00:00
-- url     : https://prove2.me/submissions/52b5da8d-3258-49c0-8489-050a0ed4e8b5

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrefixProjection_stream_suffix_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
namespace QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
theorem _root_.solution:Function.Injective (input n):=by
  intro x y h
  have he:=stream_suffix_injective x.1.val y.1.val x.2 y.2
    (x.1.property.trans y.1.property.symm) h
  exact Prod.ext (Subtype.ext he.1) he.2
end QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
