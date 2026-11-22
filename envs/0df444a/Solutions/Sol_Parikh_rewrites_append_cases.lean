-- Prove2me | solution 1 for Parikh.rewrites_append_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:16.045195+00:00
-- url     : https://prove2.me/submissions/87b3fd08-8bfd-4299-9f52-ee049a5c179f

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_Parikh_GrammarTrees

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
variable {N : Type*}
namespace Parikh
theorem _root_.solution (r : ContextFreeRule T N)
    (u v w : List (Symbol T N)) (h : r.Rewrites (u ++ v) w) :
    (∃ u', r.Rewrites u u' ∧ w = u' ++ v) ∨
      (∃ v', r.Rewrites v v' ∧ w = u ++ v') := by
  induction u generalizing w with
  | nil => exact Or.inr ⟨w, h, rfl⟩
  | cons x u ih =>
    cases h with
    | head =>
      exact Or.inl ⟨r.output ++ u, .head u, (List.append_assoc _ _ _).symm⟩
    | cons _ h =>
      rcases ih _ h with ⟨u', hu', rfl⟩ | ⟨v', hv', rfl⟩
      · exact Or.inl ⟨x :: u', .cons x hu', rfl⟩
      · exact Or.inr ⟨v', hv', rfl⟩
end Parikh
