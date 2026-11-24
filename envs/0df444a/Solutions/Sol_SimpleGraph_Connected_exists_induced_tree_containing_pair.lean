-- Prove2me | solution 1 for SimpleGraph.Connected.exists_induced_tree_containing_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:25:25.020644+00:00
-- url     : https://prove2.me/submissions/15bcfde9-cce0-43b9-9793-110e2dfaa3f4

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Data.Set.Finite.Lemmas
public import Definitions.Def_Wowii84_LargestInducedTree
public import Theorems.Thm_SimpleGraph_Walk_induce_support_isTree_of_length_eq_dist

set_option autoImplicit false
@[expose] public section
public section
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [Fintype α]
namespace SimpleGraph
namespace Connected
theorem _root_.solution {G : SimpleGraph α}
    (hG : G.Connected) (x y : α) :
    ∃ s : Finset α, x ∈ s ∧ y ∈ s ∧ (G.induce (s : Set α)).IsTree := by
  obtain ⟨p, _, hp⟩ := hG.exists_path_of_dist x y
  refine ⟨p.support.toFinset, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact Walk.induce_support_isTree_of_length_eq_dist p hp
end Connected
end SimpleGraph
