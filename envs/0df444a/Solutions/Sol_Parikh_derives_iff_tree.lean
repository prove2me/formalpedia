-- Prove2me | solution 1 for Parikh.derives_iff_tree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:33.490982+00:00
-- url     : https://prove2.me/submissions/2a46a024-d64b-413f-9f28-5d931c908ab9

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Theorems.Thm_Parikh_ParseTree_frontier_holes
public import Theorems.Thm_Parikh_ParseTree_frontier_yield
public import Theorems.Thm_Parikh_ParseTree_frontier_of_holes_eq_nil
public import Theorems.Thm_Parikh_Valid_derives_frontier
public import Theorems.Thm_Parikh_derives_tree_frontier

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
variable {N : Type*}
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T) (A : g.NT) (w : List T) :
    g.Derives [.nonterminal A] (w.map Symbol.terminal) ↔
      ∃ t : ParseTree T g.NT,
        Complete g t ∧ t.root = .nonterminal A ∧ t.yield = w := by
  constructor
  · intro h
    obtain ⟨t, ht, hr, hf⟩ := derives_tree_frontier g A h
    refine ⟨t, ⟨ht, ?_⟩, hr, ?_⟩
    · rw [← t.frontier_holes, hf]
      simp
    · rw [← t.frontier_yield, hf]
      simp
  · rintro ⟨t, ⟨ht, hh⟩, hr, hw⟩
    simpa only [hr, t.frontier_of_holes_eq_nil hh, hw] using ht.derives_frontier
end Parikh
