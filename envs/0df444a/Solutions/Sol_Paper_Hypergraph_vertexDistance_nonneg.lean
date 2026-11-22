-- Prove2me | solution 1 for Paper.Hypergraph.vertexDistance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:59:14.31947+00:00
-- url     : https://prove2.me/submissions/0f489c40-c60f-4b8e-80bb-68474f98e4b8

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
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {u v : ℕ} (hu : u ∈ H.vertices) :
    0 ≤ H.vertexDistance x u v := by
  refine le_csInf ⟨1, Set.mem_insert _ _⟩ ?_
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · norm_num
  · exact sum_nonneg (fun z hz => hx z (H.walk_vertices p hu z (List.mem_toFinset.mp hz)))
end Paper.Hypergraph
