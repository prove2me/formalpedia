-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection.fields_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:15:09.004202+00:00
-- url     : https://prove2.me/submissions/96b0c6df-1035-4d1c-8d90-c51346da543b

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
namespace QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
theorem _root_.solution (i:ℕ) (xs:List ℕ):fields n (allMask n) i xs=xs:=by
  induction xs generalizing i with
  | nil=>rfl
  | cons a xs ih=>simp only [fields,maskAt,allMask,↓reduceIte,ih]
end QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
