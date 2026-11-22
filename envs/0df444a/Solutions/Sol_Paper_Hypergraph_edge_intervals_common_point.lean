-- Prove2me | solution 1 for Paper.Hypergraph.edge_intervals_common_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:29.220329+00:00
-- url     : https://prove2.me/submissions/9df33ab8-4088-449c-949d-cb00d55ed08f

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x d : ℕ → ℝ}
    (hstep : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → d v ≤ d u + x v)
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {e : ℕ} (he : e ∈ H.edges) :
    ∃ q : ℝ, ∀ v ∈ H.edge e, d v - x v ≤ q ∧ q ≤ d v := by
  obtain ⟨u, hu, hmin⟩ := (H.edge e).exists_min_image d (H.edge_nonempty e he)
  refine ⟨d u, ?_⟩
  intro v hv
  refine ⟨?_, hmin v hv⟩
  by_cases huv : u = v
  · subst v
    have := hx u (H.edge_subset e he hu)
    linarith
  · have h := hstep u (H.edge_subset e he hu) v (H.edge_subset e he hv) ⟨huv, e, he, hu, hv⟩
    linarith
end Paper.Hypergraph
