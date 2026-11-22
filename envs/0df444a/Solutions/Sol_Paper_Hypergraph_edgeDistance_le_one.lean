-- Prove2me | solution 1 for Paper.Hypergraph.edgeDistance_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:30.929402+00:00
-- url     : https://prove2.me/submissions/c4fbf97b-82da-43e9-9c2d-1ef538a5d2e3

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_one
import Theorems.Thm_Paper_Hypergraph_edgeDistance_le_vertexDistance

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {e f : ℕ}
    (he : e ∈ H.edges) (hf : f ∈ H.edges) : H.edgeDistance x e f ≤ 1 := by
  obtain ⟨u, hu⟩ := H.edge_nonempty e he
  obtain ⟨v, hv⟩ := H.edge_nonempty f hf
  exact (H.edgeDistance_le_vertexDistance hx he hu hv).trans
    (H.vertexDistance_le_one hx (H.edge_subset e he hu))
end Paper.Hypergraph
