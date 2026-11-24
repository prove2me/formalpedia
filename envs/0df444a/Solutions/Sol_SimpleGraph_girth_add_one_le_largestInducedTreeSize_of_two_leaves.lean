-- Prove2me | solution 1 for SimpleGraph.girth_add_one_le_largestInducedTreeSize_of_two_leaves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:51.838444+00:00
-- url     : https://prove2.me/submissions/241f12b8-6ea9-4af1-a597-cd01d7a66067

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Data.Set.Finite.Lemmas
public import Definitions.Def_Wowii84_LargestInducedTree
public import Theorems.Thm_SimpleGraph_card_le_largestInducedTreeSize
public import Theorems.Thm_SimpleGraph_Connected_exists_induced_tree_containing_pair
public import Theorems.Thm_SimpleGraph_exists_maximum_induced_tree_containing
public import Theorems.Thm_SimpleGraph_exists_two_adj_of_maximum_induced_tree_containing
public import Theorems.Thm_SimpleGraph_IsTree_girth_add_one_le_card_of_two_leaves_of_two_adj

set_option autoImplicit false
@[expose] public section
public section
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace SimpleGraph
theorem _root_.solution
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hcyc : ¬ G.IsAcyclic)
    {x y : α} (hxy : x ≠ y)
    (hx : G.degree x = 1) (hy : G.degree y = 1) :
    G.girth + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨t, hxt, hyt, hTt⟩ :=
    Connected.exists_induced_tree_containing_pair hG x y
  have hr : ∃ u : Finset α,
      ({x, y} : Finset α) ⊆ u ∧ (G.induce (u : Set α)).IsTree := by
    refine ⟨t, ?_, hTt⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hxt
    · have hvy : v = y := Finset.mem_singleton.mp hv
      subst v
      exact hyt
  obtain ⟨s, hrs, hT, hmax⟩ :=
    exists_maximum_induced_tree_containing G {x, y} hr
  have hxs : x ∈ s := hrs (by simp)
  have hys : y ∈ s := hrs (by simp)
  have hs : s.Nonempty := ⟨x, hxs⟩
  have hsu : s ≠ Finset.univ := by
    intro hsu
    subst s
    have hset : (↑(Finset.univ : Finset α) : Set α) = Set.univ := by
      ext v
      simp
    rw [hset] at hT
    have hTuniv : (G.induce Set.univ).IsTree := hT
    have hGtree : G.IsTree := (induceUnivIso G).isTree_iff.mp hTuniv
    exact hcyc hGtree.isAcyclic
  obtain ⟨z, hz, a, ha, b, hb, hab, hza, hzb⟩ :=
    exists_two_adj_of_maximum_induced_tree_containing
      hG hrs hs hT hmax hsu
  have hbound : G.girth + 1 ≤ s.card :=
    IsTree.girth_add_one_le_card_of_two_leaves_of_two_adj
      hT hxs hys hxy hx hy hz ha hb hab hza hzb
  exact hbound.trans (card_le_largestInducedTreeSize hT)
end SimpleGraph
