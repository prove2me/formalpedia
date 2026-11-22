-- Prove2me | solution 1 for Paper.Hypergraph.vertexDistance_le_option
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:39.610505+00:00
-- url     : https://prove2.me/submissions/5dc8cc1d-0585-46b5-915d-427a7f993b5e

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_walk_vertices

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {u v : ℕ} (hu : u ∈ H.vertices)
    {r : ℝ} (hr : r ∈ insert 1 {r | ∃ p : H.primal.Walk u v,
      p.IsPath ∧ r = ∑ z ∈ p.support.toFinset, x z}) : H.vertexDistance x u v ≤ r := by
  refine csInf_le ⟨0, ?_⟩ hr
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · norm_num
  · exact sum_nonneg (fun z hz => hx z (H.walk_vertices p hu z (List.mem_toFinset.mp hz)))
end Paper.Hypergraph
