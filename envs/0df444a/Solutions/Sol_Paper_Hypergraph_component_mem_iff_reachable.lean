-- Prove2me | solution 1 for Paper.Hypergraph.component_mem_iff_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:24.798958+00:00
-- url     : https://prove2.me/submissions/4eee8d66-1715-42f0-846c-672635f85022

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
theorem _root_.solution (H : Hypergraph) {K : Finset ℕ}
    (hK : K ∈ H.components) {u v : ℕ} (hu : u ∈ K) (hv : v ∈ H.vertices) :
    v ∈ K ↔ H.primal.Reachable u v := by
  obtain ⟨hKV, a, ha, hr⟩ := mem_filter.mp hK
  have hsub : K ⊆ H.vertices := mem_powerset.mp hKV
  have hau := (hr u (hsub hu)).mp hu
  constructor
  · intro hvK
    exact hau.symm.trans ((hr v hv).mp hvK)
  · intro huv
    exact (hr v hv).mpr (hau.trans huv)
end Paper.Hypergraph
