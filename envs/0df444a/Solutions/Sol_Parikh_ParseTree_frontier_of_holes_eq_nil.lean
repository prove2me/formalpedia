-- Prove2me | solution 1 for Parikh.ParseTree.frontier_of_holes_eq_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:16.402148+00:00
-- url     : https://prove2.me/submissions/3e22399f-0ba6-430a-a385-2c49f233e056

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Theorems.Thm_Parikh_ParseTree_frontier_holes
public import Theorems.Thm_Parikh_ParseTree_frontier_yield

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
variable {N : Type*}
open Parikh.ParseTree
namespace Parikh.ParseTree
theorem _root_.solution (t : ParseTree T N) (h : t.holes = []) :
    t.frontier = t.yield.map Symbol.terminal := by
  have onlyTerminals : ∀ l : List (Symbol T N),
      (l.filterMap fun s => match s with
        | .terminal _ => none | .nonterminal A => some A) = [] →
      l = (l.filterMap fun s => match s with
        | .terminal a => some a | .nonterminal _ => none).map Symbol.terminal := by
    intro l
    induction l with
    | nil => simp
    | cons s l ih =>
      cases s with
      | terminal a =>
        intro h
        simp only [List.filterMap_cons_none] at h
        simpa only [List.filterMap_cons, List.map_cons]
          using congrArg (Symbol.terminal a :: ·) (ih h)
      | nonterminal A => simp
  rw [← frontier_yield]
  exact onlyTerminals t.frontier (t.frontier_holes.trans h)
end Parikh.ParseTree
