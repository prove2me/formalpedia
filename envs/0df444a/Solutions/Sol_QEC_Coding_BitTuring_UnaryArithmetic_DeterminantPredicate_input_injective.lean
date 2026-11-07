-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:37.187208+00:00
-- url     : https://prove2.me/submissions/076d9dc5-125d-46f7-945f-a62762df2332

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryQuaternionMatrix
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryDeterminantPredicate
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection QuaternionAssembly
namespace QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate
theorem _root_.solution:Function.Injective input:=by
  intro x y hh
  have he:=stream_injective hh
  cases x with
  | mk a b c d q hq=>
    cases y with
    | mk a' b' c' d' q' hq'=>
      change [a,b,c,d,q]=[a',b',c',d',q'] at he
      simp only [List.cons.injEq] at he
      rcases he with ⟨rfl,rfl,rfl,rfl,rfl,_⟩
      rfl
end QEC.Coding.BitTuring.UnaryArithmetic.DeterminantPredicate
