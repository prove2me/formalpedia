-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ModularDot.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:16:51.802198+00:00
-- url     : https://prove2.me/submissions/f5135bd9-d55e-4907-bd74-3a49d1125200

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularSum
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularDot
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularDot
open Turing
open FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularDot
theorem _root_.solution : Function.Injective input := by
  intro x y hh
  have he:=stream_injective hh
  cases x with
  | mk a b c d q=>
    cases y with
    | mk a' b' c' d' q'=>
      change [a,b,c,d,q.val]=[a',b',c',d',q'.val] at he
      simp only [List.cons.injEq] at he
      rcases he with ⟨rfl,rfl,rfl,rfl,hq,_⟩
      have hq':q=q':=Subtype.ext hq
      subst q';rfl
end QEC.Coding.BitTuring.UnaryArithmetic.ModularDot
