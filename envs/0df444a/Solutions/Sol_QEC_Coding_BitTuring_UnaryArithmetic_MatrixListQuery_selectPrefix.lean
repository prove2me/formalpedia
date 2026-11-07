-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.MatrixListQuery.selectPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:56:50.074207+00:00
-- url     : https://prove2.me/submissions/39893929-b8f7-4707-8e58-0e4d048819e3

import Definitions.Def_QEC_Coding_BitTuring_ModulusQuery
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixListQuery

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.MatrixListQuery
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
namespace QEC.Coding.BitTuring.UnaryArithmetic.MatrixListQuery
theorem _root_.solution (n i:ℕ) (xs:List ℕ) (q:ℕ) (hi:i+xs.length=n) :
    fields n (prefixMask n) i (xs++[q])=xs := by
  induction xs generalizing i with
  | nil=>
    have he:i=n :=by simpa using hi
    subst i
    simp [fields,maskAt,prefixMask,Nat.mod_eq_of_lt (show n<n+1 by omega)]
  | cons x xs ih=>
    have hl:i<n :=by simp only [List.length_cons] at hi;omega
    have ht:i+1+xs.length=n :=by simp only [List.length_cons] at hi;omega
    simp only [List.cons_append,fields,maskAt,prefixMask,
      Nat.mod_eq_of_lt (show i<n+1 by omega),hl,decide_true,↓reduceIte]
    congr 1
    exact ih (i+1) ht
end QEC.Coding.BitTuring.UnaryArithmetic.MatrixListQuery
