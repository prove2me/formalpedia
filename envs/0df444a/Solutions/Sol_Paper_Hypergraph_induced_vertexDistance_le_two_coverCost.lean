-- Prove2me | solution 1 for Paper.Hypergraph.induced_vertexDistance_le_two_coverCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:05.554153+00:00
-- url     : https://prove2.me/submissions/d95fa630-bc6f-4a8a-8193-d02c32672eeb

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
import Theorems.Thm_Paper_Hypergraph_restrictDemand_cost_le
import Theorems.Thm_Paper_Hypergraph_demand_sum_le_card_bound_mul_coverCost
import Theorems.Thm_Paper_Hypergraph_shortest_induced_path_edge_card
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_walk
import Theorems.Thm_Paper_Hypergraph_walk_vertices


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ z ∈ H.vertices, 0 ≤ x z) (Q : Finset ℕ) {u v : ℕ}
    (hu : u ∈ (H.induce Q).vertices) (huv : (H.induce Q).primal.Reachable u v) :
    (H.induce Q).vertexDistance x u v ≤ 2 * H.coverCost x := by
  obtain ⟨p, hp⟩ := huv.exists_walk_length_eq_dist
  have hS : p.support.toFinset ⊆ H.vertices := by
    intro z hz
    exact (mem_inter.mp ((H.induce Q).walk_vertices p hu z (List.mem_toFinset.mp hz))).1
  have hcard : ∀ e ∈ H.edges, (p.support.toFinset ∩ H.edge e).card ≤ 2 := by
    intro e he
    exact H.shortest_induced_path_edge_card Q hu p hp (fun _ hz => List.mem_toFinset.mp hz) he
  calc
    _ ≤ ∑ z ∈ p.support.toFinset, x z :=
      (H.induce Q).vertexDistance_le_walk (fun z hz => hx z (mem_inter.mp hz).1) hu p
    _ ≤ 2 * H.coverCost (restrictDemand x p.support.toFinset) := by
      simpa using H.demand_sum_le_card_bound_mul_coverCost x hS hcard
    _ ≤ _ := mul_le_mul_of_nonneg_left (H.restrictDemand_cost_le hx _) (by norm_num)
end Paper.Hypergraph
