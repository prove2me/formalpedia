-- Prove2me | solution 1 for Paper.Hypergraph.vertexDistance_le_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:30.375799+00:00
-- url     : https://prove2.me/submissions/10150f09-705d-4d5c-b7a3-344ca1515b8f

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_one
import Theorems.Thm_Paper_Hypergraph_primal_induce_le
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_option


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (Q : Finset ℕ)
    {u v : ℕ} (hu : u ∈ H.vertices) :
    H.vertexDistance x u v ≤ (H.induce Q).vertexDistance x u v := by
  apply le_csInf ⟨1, Set.mem_insert _ _⟩
  rintro r (rfl | ⟨p, hp, rfl⟩)
  · exact H.vertexDistance_le_one hx hu
  · apply H.vertexDistance_le_option hx hu
    refine Set.mem_insert_of_mem 1 ⟨p.mapLe (H.primal_induce_le Q), hp.mapLe _, ?_⟩
    rw [SimpleGraph.Walk.support_mapLe_eq_support]
end Paper.Hypergraph
