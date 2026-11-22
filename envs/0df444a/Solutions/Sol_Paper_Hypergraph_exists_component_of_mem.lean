-- Prove2me | solution 1 for Paper.Hypergraph.exists_component_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:16.068811+00:00
-- url     : https://prove2.me/submissions/7a0f12ac-b25f-4a29-a238-af4dd5f44a21

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {u : ℕ} (hu : u ∈ H.vertices) :
    ∃ K ∈ H.components, u ∈ K := by
  let K := H.vertices.filter (fun v => H.primal.Reachable u v)
  have huK : u ∈ K := mem_filter.mpr ⟨hu, .rfl⟩
  refine ⟨K, mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), u, huK, ?_⟩, huK⟩
  intro v hv
  simp only [K, mem_filter, hv, true_and]
end Paper.Hypergraph
