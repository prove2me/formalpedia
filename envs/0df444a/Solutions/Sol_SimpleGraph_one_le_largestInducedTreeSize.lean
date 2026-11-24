-- Prove2me | solution 1 for SimpleGraph.one_le_largestInducedTreeSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:39.94442+00:00
-- url     : https://prove2.me/submissions/f58f1ef4-7654-4059-94b4-b74974c420e6

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Data.Set.Finite.Lemmas
public import Definitions.Def_Wowii84_LargestInducedTree
public import Theorems.Thm_SimpleGraph_card_le_largestInducedTreeSize

set_option autoImplicit false
@[expose] public section
public section
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α]
namespace SimpleGraph
theorem _root_.solution (G : SimpleGraph α) [Nonempty α] :
    1 ≤ largestInducedTreeSize G := by
  classical
  let x : α := Classical.choice (inferInstance : Nonempty α)
  let s : Finset α := {x}
  have hs : (s : Set α) = {x} := by
    simp [s]
  have hT : (G.induce (s : Set α)).IsTree := by
    rw [hs]
    let : Nonempty ↥({x} : Set α) := ⟨⟨x, by simp⟩⟩
    let : Subsingleton ↥({x} : Set α) := ⟨fun a b => by
      apply Subtype.ext
      have ha : (a : α) = x := Set.mem_singleton_iff.mp a.property
      have hb : (b : α) = x := Set.mem_singleton_iff.mp b.property
      exact ha.trans hb.symm⟩
    exact IsTree.of_subsingleton
  have hle := card_le_largestInducedTreeSize hT
  simpa [s] using hle
end SimpleGraph
