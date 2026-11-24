-- Prove2me | solution 1 for SimpleGraph.exists_two_adj_of_maximum_induced_tree_containing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:31:56.479426+00:00
-- url     : https://prove2.me/submissions/bd19415e-35f1-438c-b819-5c78d335bacf

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Data.Set.Finite.Lemmas
public import Definitions.Def_Wowii84_LargestInducedTree
public import Theorems.Thm_SimpleGraph_IsTree_induce_insert_of_unique_adj
public import Theorems.Thm_SimpleGraph_Connected_exists_adj_finset_compl

set_option autoImplicit false
@[expose] public section
public section
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace SimpleGraph
theorem _root_.solution
    {G : SimpleGraph α} {r s : Finset α}
    (hG : G.Connected) (hrs : r ⊆ s) (hs : s.Nonempty)
    (hT : (G.induce (s : Set α)).IsTree)
    (hmax : ∀ t : Finset α, r ⊆ t →
      (G.induce (t : Set α)).IsTree → t.card ≤ s.card)
    (hsu : s ≠ Finset.univ) :
    ∃ z ∉ s, ∃ a ∈ s, ∃ b ∈ s,
      a ≠ b ∧ G.Adj z a ∧ G.Adj z b := by
  obtain ⟨z, hz, a, ha, hza⟩ := hG.exists_adj_finset_compl hs hsu
  by_cases hex : ∃ b ∈ s, b ≠ a ∧ G.Adj z b
  · obtain ⟨b, hb, hba, hzb⟩ := hex
    exact ⟨z, hz, a, ha, b, hb, hba.symm, hza, hzb⟩
  · have huniq : ∀ ⦃b : α⦄, b ∈ s → G.Adj z b → b = a := by
      intro b hb hzb
      by_contra hba
      exact hex ⟨b, hb, hba, hzb⟩
    have hT' := hT.induce_insert_of_unique_adj hz ha hza huniq
    have hrs' : r ⊆ insert z s := by
      intro v hv
      exact Finset.mem_insert_of_mem (hrs hv)
    have hle := hmax (insert z s) hrs' hT'
    have hcard := Finset.card_insert_of_notMem hz
    omega
end SimpleGraph
