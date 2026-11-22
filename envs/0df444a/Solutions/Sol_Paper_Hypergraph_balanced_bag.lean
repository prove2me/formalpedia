-- Prove2me | solution 1 for Paper.Hypergraph.balanced_bag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:01.520523+00:00
-- url     : https://prove2.me/submissions/2d9fb305-56af-4b7c-9457-962504a21b22

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_component_mem_iff_reachable
import Theorems.Thm_Paper_Hypergraph_tree_weighted_median
import Theorems.Thm_Paper_Hypergraph_tree_branch_distance
import Theorems.Thm_Paper_Hypergraph_TreeDecomposition_walk_avoiding

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : H.EdgeWeight γ) {n : ℕ} (D : H.TreeDecomposition n) :
    ∃ t, H.IntegralBalanced γ (1 / 2) (D.bag t) := by
  classical
  let assign : ℕ → Fin (n + 1) := fun e =>
    if he : e ∈ H.edges then (D.edge_covered e he).choose else 0
  have ha (e : ℕ) (he : e ∈ H.edges) : H.edge e ⊆ D.bag (assign e) := by
    simpa [assign, he] using (D.edge_covered e he).choose_spec
  obtain ⟨t, ht⟩ := tree_weighted_median D.tree D.isTree H.edges assign γ
    (fun e he => (hγ.1 e he).1)
  refine ⟨t, D.bag_subset t, ?_⟩
  intro K hK
  let J := H.induce (H.vertices \ D.bag t)
  have hKJ : K ⊆ J.vertices := mem_powerset.mp (mem_filter.mp hK).1
  obtain ⟨v, hvK, _⟩ := (mem_filter.mp hK).2
  have hv := hKJ hvK
  have hvt : v ∉ D.bag t := (mem_sdiff.mp (mem_inter.mp hv).2).2
  obtain ⟨u, hvu⟩ := D.vertex_covered v (mem_inter.mp hv).1
  have hut : u ≠ t := fun h => hvt (h ▸ hvu)
  obtain ⟨p, hp, _⟩ := (D.isTree.connected t u).exists_path_of_dist
  cases p with
  | nil => exact (hut rfl).elim
  | @cons _ r _ htr p =>
    have hp' := (SimpleGraph.Walk.cons_isPath_iff htr p).mp hp
    have hsupp : ∀ s ∈ p.support, s ∈ {s | s ≠ t} := by
      intro s hs hst
      exact hp'.2 (hst ▸ hs)
    have hru : (D.tree.induce {s | s ≠ t}).Reachable ⟨r, htr.ne.symm⟩ ⟨u, hut⟩ :=
      ⟨p.induce _ hsupp⟩
    have hdrop : H.edges.filter (fun e => ¬ Disjoint (H.edge e) K) ⊆
        H.edges.filter (fun e => D.tree.dist t (assign e) = D.tree.dist r (assign e) + 1) := by
      intro e he
      obtain ⟨heE, heK⟩ := mem_filter.mp he
      obtain ⟨w, hwe, hwK⟩ := not_disjoint_iff.mp heK
      have hw := hKJ hwK
      have hwa : w ∈ D.bag (assign e) := ha e heE hwe
      have hwat : assign e ≠ t := fun h =>
        (mem_sdiff.mp (mem_inter.mp hw).2).2 (h ▸ hwa)
      have hrw : J.primal.Reachable v w :=
        (J.component_mem_iff_reachable hK hvK hw).mp hwK
      have hutow := D.walk_avoiding t hrw.some hv hvu hwa hut hwat
      exact mem_filter.mpr ⟨heE, tree_branch_distance D.isTree htr hwat (hru.trans hutow)⟩
    exact (sum_le_sum_of_subset_of_nonneg hdrop
      (fun e he _ => (hγ.1 e (mem_filter.mp he).1).1)).trans (ht r htr)
end Paper.Hypergraph
