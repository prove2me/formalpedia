-- Prove2me | solution 1 for Parikh.derives_tree_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:45.999783+00:00
-- url     : https://prove2.me/submissions/646c665e-08ae-446e-836a-95a6e4170354

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Theorems.Thm_Parikh_Valid_frontier_step

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
variable {N : Type*}
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T) (A : g.NT)
    {v : List (Symbol T g.NT)} (h : g.Derives [.nonterminal A] v) :
    ∃ t, Valid g t ∧ t.root = .nonterminal A ∧ t.frontier = v := by
  induction h with
  | refl => exact ⟨.hole A, .hole A, rfl, by simp [ParseTree.frontier]⟩
  | tail h step ih =>
    obtain ⟨t, ht, hr, hf⟩ := ih
    obtain ⟨t', ht', hr', hf'⟩ := ht.frontier_step (hf.symm ▸ step)
    exact ⟨t', ht', hr'.trans hr, hf'⟩
end Parikh
