-- Prove2me | solution 1 for Parikh.ParseTree.frontier_holes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:36.628923+00:00
-- url     : https://prove2.me/submissions/2595e764-35a1-410d-8fb2-26a37ea9d629

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
      | .terminal _ => none | .nonterminal A => some A) = t.holes := by
  induction t using ParseTree.rec (motive_2 := fun (ts : List (ParseTree T N)) =>
    ∀ t ∈ ts, (t.frontier.filterMap fun (s : Symbol T N) => match s with
      | .terminal _ => none | .nonterminal A => some A) = t.holes) with
  | terminal a => simp [frontier, holes]
  | hole A => simp [frontier, holes]
  | node r children ih =>
    simp only [frontier, holes, List.filterMap_flatten, List.map_map]
    congr 1
    exact List.map_congr_left ih
  | nil c hc => simp at hc
  | cons t ts ht hts c hc =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ht
    · exact hts c hc
end Parikh.ParseTree
