-- Prove2me | solution 1 for Paper.Hypergraph.shortest_path_clique_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:30:26.631856+00:00
-- url     : https://prove2.me/submissions/8c0ba3f3-05c9-4ee7-81b3-4f8e8b6ca4ff

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
import Theorems.Thm_Paper_Hypergraph_shortest_path_prefix_distance

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {G : SimpleGraph ℕ} {u v : ℕ}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (S : Finset ℕ)
    (hS : ∀ z ∈ S, z ∈ p.support)
    (hclique : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b) : S.card ≤ 2 := by
  have hinj : Set.InjOn (G.dist u) (↑S : Set ℕ) := by
    intro a ha b hb heq
    obtain ⟨i, hi, hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hS a ha)
    obtain ⟨j, hj, hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hS b hb)
    have hdi := shortest_path_prefix_distance p hp hil
    have hdj := shortest_path_prefix_distance p hp hjl
    rw [hi] at hdi
    rw [hj] at hdj
    have hij : i = j := by omega
    exact hi.symm.trans ((congrArg p.getVert hij).trans hj)
  by_cases hne : S.Nonempty
  · obtain ⟨a, ha, hmin⟩ := S.exists_min_image (G.dist u) hne
    have hmap : Set.MapsTo (G.dist u) (↑S : Set ℕ)
        (↑(Finset.Icc (G.dist u a) (G.dist u a + 1)) : Set ℕ) := by
      intro b hb
      apply mem_Icc.mpr
      refine ⟨hmin b hb, ?_⟩
      by_cases hab : a = b
      · subst b
        omega
      · have hadj := hclique a ha b hb hab
        have ht := hadj.reachable.dist_triangle_right u
        rw [G.dist_eq_one_iff_adj.mpr hadj] at ht
        exact ht
    have := card_le_card_of_injOn (G.dist u) hmap hinj
    simp only [Nat.card_Icc] at this
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
end Paper.Hypergraph
