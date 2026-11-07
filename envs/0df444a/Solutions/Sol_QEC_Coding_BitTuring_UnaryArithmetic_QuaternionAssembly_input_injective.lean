-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:39:12.496009+00:00
-- url     : https://prove2.me/submissions/14692e63-1027-4570-9802-407fa2465a8a

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularAdjugate
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularSum
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Definitions.Def_QEC_Coding_BitTuring_ModulusQuery
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_BitTuring_UnaryQuaternionMatrix
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly
open Turing StateTransition FieldProjection
open Turing StateTransition FieldProjection
open Turing FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly
theorem _root_.solution : Function.Injective input := by
  intro x y hh
  have he:=stream_injective hh
  cases x with
  | mk S Y D C B A q hc=>
    cases y with
    | mk S' Y' D' C' B' A' q' hc'=>
      change [S,Y,D,C,B,A,q.val]=[S',Y',D',C',B',A',q'.val] at he
      simp only [List.cons.injEq] at he
      rcases he with ⟨rfl,rfl,rfl,rfl,rfl,rfl,hq,_⟩
      have hq':q=q':=Subtype.ext hq
      subst q';rfl
end QEC.Coding.BitTuring.UnaryArithmetic.QuaternionAssembly
