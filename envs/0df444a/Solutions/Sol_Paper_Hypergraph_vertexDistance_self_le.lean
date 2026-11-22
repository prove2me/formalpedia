-- Prove2me | solution 1 for Paper.Hypergraph.vertexDistance_self_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:34.143074+00:00
-- url     : https://prove2.me/submissions/f7a42eb1-312e-4578-8df6-0c8aafee344c

import Definitions.Def_Paper_RoundingEstimates
import Definitions.Def_Paper_RoundingGeometry
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_walk

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {u : ℕ} (hu : u ∈ H.vertices) :
    H.vertexDistance x u u ≤ x u := by
  simpa using H.vertexDistance_le_walk hx hu (.nil : H.primal.Walk u u)
end Paper.Hypergraph
