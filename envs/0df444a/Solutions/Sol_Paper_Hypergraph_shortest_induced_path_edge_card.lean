-- Prove2me | solution 1 for Paper.Hypergraph.shortest_induced_path_edge_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:21.210819+00:00
-- url     : https://prove2.me/submissions/a285fa04-83c5-4072-a237-2120f16a1317

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
import Theorems.Thm_Paper_Hypergraph_shortest_path_clique_card_le_two
import Theorems.Thm_Paper_Hypergraph_primal_induce_adj
import Theorems.Thm_Paper_Hypergraph_walk_vertices


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (Q : Finset ℕ) {u v : ℕ}
    (hu : u ∈ (H.induce Q).vertices) (p : (H.induce Q).primal.Walk u v)
    (hp : p.length = (H.induce Q).primal.dist u v) {S : Finset ℕ}
    (hS : ∀ z ∈ S, z ∈ p.support) {e : ℕ} (he : e ∈ H.edges) :
    (S ∩ H.edge e).card ≤ 2 := by
  apply shortest_path_clique_card_le_two p hp
  · intro z hz
    exact hS z (mem_inter.mp hz).1
  · intro a ha b hb hab
    have haQ := (mem_inter.mp ((H.induce Q).walk_vertices p hu a (hS a (mem_inter.mp ha).1))).2
    have hbQ := (mem_inter.mp ((H.induce Q).walk_vertices p hu b (hS b (mem_inter.mp hb).1))).2
    apply (H.primal_induce_adj Q haQ hbQ).2
    exact ⟨hab, e, he, (mem_inter.mp ha).2, (mem_inter.mp hb).2⟩
end Paper.Hypergraph
