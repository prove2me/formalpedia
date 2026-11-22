-- Prove2me | solution 1 for Paper.Hypergraph.degeneracyLevelCover_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:26.35504+00:00
-- url     : https://prove2.me/submissions/52a45a9e-c292-4ccf-b94d-04ba9bb915c5

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy
import Theorems.Thm_Paper_Hypergraph_vertexMultiplier_nonneg


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (rank : ℕ ⊕ ℕ → ℕ) {x d y q : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (hy : ∀ e ∈ H.edges, 0 ≤ y e)
    {e : ℕ} (he : e ∈ H.edges) (r : ℝ) : 0 ≤ H.degeneracyLevelCover rank x d y q e r := by
  have hye := hy e he
  apply add_nonneg
  · apply sum_nonneg
    intro v hv
    exact mul_nonneg (by positivity) (vertexMultiplier_nonneg (hx v (H.edge_subset e he (mem_filter.mp hv).1)) r)
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
end Paper.Hypergraph
