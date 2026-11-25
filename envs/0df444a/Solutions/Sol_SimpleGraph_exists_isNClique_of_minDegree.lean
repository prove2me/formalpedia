-- Prove2me | solution 1 for SimpleGraph.exists_isNClique_of_minDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:57.559705+00:00
-- url     : https://prove2.me/submissions/f39b18fe-6df9-4ad1-9ef5-26ed2cbda82a

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_spine
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_spine
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_pool
public import Theorems.Thm_SimpleGraph_Reservoir_exists_isNClique_of_card_nonadj_le
attribute [local simp] SimpleGraph.Reservoir.ofPool_spine
attribute [local simp] SimpleGraph.Reservoir.ofPool_pool
attribute [local simp] SimpleGraph.Reservoir.pivot_spine
attribute [local simp] SimpleGraph.Reservoir.pivot_pool

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
namespace SimpleGraph
theorem _root_.solution [Fintype V] [DecidableRel G.Adj] {j : ℕ}
    (hj : j * (Fintype.card V - G.minDegree) < Fintype.card V) :
    ∃ s, G.IsNClique (j + 1) s := by
  have hd : ∀ v ∈ (Reservoir.ofPool (G := G) univ).pool,
      #{w ∈ (Reservoir.ofPool (G := G) univ).pool | ¬G.Adj v w} ≤
        Fintype.card V - G.minDegree := by
    intro v _
    have hdeg : #{w ∈ (univ : Finset V) | G.Adj v w} = G.degree v := by
      rw [← card_neighborFinset_eq_degree]
      congr 1
      ext; simp
    have h := card_filter_add_card_filter_not (s := (univ : Finset V)) (G.Adj v)
    rw [hdeg, card_univ] at h
    have := G.minDegree_le_degree v
    rw [Reservoir.ofPool_pool]
    omega
  simpa using (Reservoir.ofPool (G := G) univ).exists_isNClique_of_card_nonadj_le hd j
    (by simpa using hj)
end SimpleGraph
