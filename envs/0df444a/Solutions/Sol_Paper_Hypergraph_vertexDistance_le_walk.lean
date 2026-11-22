-- Prove2me | solution 1 for Paper.Hypergraph.vertexDistance_le_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:24.763187+00:00
-- url     : https://prove2.me/submissions/c44a8e80-62ad-4df8-abf6-1a2e006559f7

import Definitions.Def_Paper_RoundingEstimates
import Definitions.Def_Paper_RoundingGeometry
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_option
import Theorems.Thm_Paper_Hypergraph_walk_vertices


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {u v : ℕ} (hu : u ∈ H.vertices)
    (p : H.primal.Walk u v) :
    H.vertexDistance x u v ≤ ∑ z ∈ p.support.toFinset, x z := by
  apply (H.vertexDistance_le_option hx hu
    (Set.mem_insert_of_mem 1 ⟨p.bypass, p.bypass_isPath, rfl⟩)).trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro z hz
    exact List.mem_toFinset.mpr (p.support_bypass_subset_support (List.mem_toFinset.mp hz))
  · intro z hz _
    exact hx z (H.walk_vertices p hu z (List.mem_toFinset.mp hz))
end Paper.Hypergraph
