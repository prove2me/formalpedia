-- Prove2me | solution 1 for Paper.Hypergraph.sum_incidence_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:51.699605+00:00
-- url     : https://prove2.me/submissions/2894adae-30a7-4a1d-bf2f-dd93a5f2190c

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (f : ℕ → ℕ → ℝ) :
    (∑ v ∈ H.vertices, ∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), f v e) =
      ∑ e ∈ H.edges, ∑ v ∈ H.edge e, f v e := by
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  rw [← sum_filter]
  congr 1
  ext v
  simp only [mem_filter]
  exact ⟨And.right, fun hv => ⟨H.edge_subset e he hv, hv⟩⟩
end Paper.Hypergraph
