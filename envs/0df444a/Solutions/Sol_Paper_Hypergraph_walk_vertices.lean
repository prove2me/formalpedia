-- Prove2me | solution 1 for Paper.Hypergraph.walk_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:14.844316+00:00
-- url     : https://prove2.me/submissions/e6dfaa85-84fd-4700-9a30-c99ee159bbc0

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
theorem _root_.solution (H : Hypergraph) {u v : ℕ} (p : H.primal.Walk u v)
    (hu : u ∈ H.vertices) : ∀ z ∈ p.support, z ∈ H.vertices := by
  induction p with
  | nil => simpa using hu
  | @cons u v t huv p ih =>
    intro z hz
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · obtain ⟨_, e, he, _, hve⟩ := huv
      exact ih (H.edge_subset e he hve) z hz
end Paper.Hypergraph
