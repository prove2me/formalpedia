-- Prove2me | solution 1 for Paper.Hypergraph.vertexDistance_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:40.149789+00:00
-- url     : https://prove2.me/submissions/aa9c1143-91b5-4f97-bb44-83dca5a4d0f4

import Definitions.Def_Paper_RoundingEstimates
import Definitions.Def_Paper_RoundingGeometry
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_walk
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_one
import Theorems.Thm_Paper_Hypergraph_walk_vertices


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x y : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v)
    (hxy : ∀ v ∈ H.vertices, x v ≤ y v) {u v : ℕ} (hu : u ∈ H.vertices) :
    H.vertexDistance x u v ≤ H.vertexDistance y u v := by
  apply le_csInf ⟨1, Set.mem_insert _ _⟩
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · exact H.vertexDistance_le_one hx hu
  · exact (H.vertexDistance_le_walk hx hu p).trans (sum_le_sum fun z hz =>
      hxy z (H.walk_vertices p hu z (List.mem_toFinset.mp hz)))
end Paper.Hypergraph
