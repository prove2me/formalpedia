-- Prove2me | solution 1 for Parikh.ParseTree.frontier_yield
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:37.259111+00:00
-- url     : https://prove2.me/submissions/963d1ba5-89fb-4025-be8c-d3ad7d0185ea

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
open Parikh.ParseTree
namespace Parikh.ParseTree
theorem _root_.solution (t : ParseTree T N) :
    (t.frontier.filterMap fun (s : Symbol T N) => match s with
      | .terminal a => some a | .nonterminal _ => none) = t.yield := by
  induction t using ParseTree.rec (motive_2 := fun (ts : List (ParseTree T N)) =>
    ∀ t ∈ ts, (t.frontier.filterMap fun (s : Symbol T N) => match s with
      | .terminal a => some a | .nonterminal _ => none) = t.yield) with
  | terminal a => simp [frontier, yield]
  | hole A => simp [frontier, yield]
  | node r children ih =>
    simp only [frontier, yield, List.filterMap_flatten, List.map_map]
    congr 1
    exact List.map_congr_left ih
  | nil c hc => simp at hc
  | cons t ts ht hts c hc =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ht
    · exact hts c hc
end Parikh.ParseTree
