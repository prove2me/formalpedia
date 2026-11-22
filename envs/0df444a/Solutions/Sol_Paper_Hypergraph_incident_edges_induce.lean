-- Prove2me | solution 1 for Paper.Hypergraph.incident_edges_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:18.620688+00:00
-- url     : https://prove2.me/submissions/e148f621-c90d-4b00-ad90-f72eead71a8f

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
theorem _root_.solution (H : Hypergraph) {W : Finset ℕ} {v : ℕ} (hv : v ∈ W) :
    (H.induce W).edges.filter (fun e => v ∈ (H.induce W).edge e) =
      H.edges.filter (fun e => v ∈ H.edge e) := by
  ext e
  simp only [induce, mem_filter, mem_inter]
  constructor
  · rintro ⟨⟨he, _⟩, hve, _⟩; exact ⟨he, hve⟩
  · rintro ⟨he, hve⟩
    exact ⟨⟨he, ⟨v, mem_inter.mpr ⟨hve, hv⟩⟩⟩, hve, hv⟩
end Paper.Hypergraph
