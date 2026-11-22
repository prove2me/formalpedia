-- Prove2me | solution 1 for Paper.Hypergraph.edge_subset_component
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:34.907668+00:00
-- url     : https://prove2.me/submissions/e99ead5c-82aa-4368-9b4f-4807143f7580

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_component_mem_iff_reachable

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {C : Finset ℕ} (hC : C ∈ H.components)
    {e v : ℕ} (he : e ∈ H.edges) (hve : v ∈ H.edge e) (hvC : v ∈ C) : H.edge e ⊆ C := by
  intro w hw
  apply (H.component_mem_iff_reachable hC hvC (H.edge_subset e he hw)).mpr
  by_cases hvw : v = w
  · subst w; exact SimpleGraph.Reachable.refl _
  · exact (show H.primal.Adj v w from ⟨hvw, e, he, hve, hw⟩).reachable
end Paper.Hypergraph
