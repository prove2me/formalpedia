-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ModularMatrixProduct.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:06:33.403687+00:00
-- url     : https://prove2.me/submissions/00b259f7-4add-4ddb-89ff-ebdb33a4c51b

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularDot
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixProduct
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularMatrixProduct
open Turing
open FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularMatrixProduct
theorem _root_.solution : Function.Injective input := by
  intro x y hh
  have he:=stream_injective hh
  cases x with
  | mk a b c d e f g h q=>
    cases y with
    | mk a' b' c' d' e' f' g' h' q'=>
      change [a,b,c,d,e,f,g,h,q.val]=[a',b',c',d',e',f',g',h',q'.val] at he
      simp only [List.cons.injEq] at he
      rcases he with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hq,_⟩
      have hq':q=q':=Subtype.ext hq
      subst q';rfl
end QEC.Coding.BitTuring.UnaryArithmetic.ModularMatrixProduct
