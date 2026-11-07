-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:16:41.748547+00:00
-- url     : https://prove2.me/submissions/3267bf96-dbe3-4a5c-9a35-e6a7d972ae7b

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularNegation
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularAdjugate
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate
open Turing
open FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate
theorem _root_.solution : Function.Injective input := by
  intro x y hh
  have he:=stream_injective hh
  cases x with
  | mk a b c d q hb hc=>
    cases y with
    | mk a' b' c' d' q' hb' hc'=>
      change [a,b,c,d,q.val]=[a',b',c',d',q'.val] at he
      simp only [List.cons.injEq] at he
      rcases he with ⟨rfl,rfl,rfl,rfl,hq,_⟩
      have hq':q=q':=Subtype.ext hq
      subst q';rfl
end QEC.Coding.BitTuring.UnaryArithmetic.ModularAdjugate
