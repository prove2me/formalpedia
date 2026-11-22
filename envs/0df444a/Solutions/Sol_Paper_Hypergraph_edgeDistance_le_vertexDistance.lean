-- Prove2me | solution 1 for Paper.Hypergraph.edgeDistance_le_vertexDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:21.41628+00:00
-- url     : https://prove2.me/submissions/d2da8b5c-cae2-4680-aafb-72ef3b359560

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
import Theorems.Thm_Paper_Hypergraph_vertexDistance_nonneg


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {e f u v : ℕ}
    (he : e ∈ H.edges) (hu : u ∈ H.edge e) (hv : v ∈ H.edge f) :
    H.edgeDistance x e f ≤ H.vertexDistance x u v := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨a, ha, b, hb, rfl⟩
    exact H.vertexDistance_nonneg hx (H.edge_subset e he ha)
  · exact ⟨u, hu, v, hv, rfl⟩
end Paper.Hypergraph
