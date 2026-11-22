-- Prove2me | solution 1 for Paper.Hypergraph.TreeDecomposition.same_vertex_avoiding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:34.712248+00:00
-- url     : https://prove2.me/submissions/d9eac4bb-94d0-4a52-b76c-c59db1dfa1a7

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
namespace TreeDecomposition
theorem _root_.solution {H : Hypergraph} {n : ℕ}
    (D : H.TreeDecomposition n) (t : Fin (n + 1)) {v : ℕ} (hv : v ∈ H.vertices)
    (hvt : v ∉ D.bag t) {a b : Fin (n + 1)} (ha : v ∈ D.bag a) (hb : v ∈ D.bag b) :
    (D.tree.induce {s | s ≠ t}).Reachable
      ⟨a, fun h => hvt (h ▸ ha)⟩ ⟨b, fun h => hvt (h ▸ hb)⟩ := by
  have hsub : {s | v ∈ D.bag s} ⊆ {s | s ≠ t} := by
    intro s hs hst
    exact hvt (hst ▸ hs)
  exact ((D.running_intersection v hv) ⟨a, ha⟩ ⟨b, hb⟩).map
    (D.tree.induceHomOfLE hsub).toHom
end TreeDecomposition
end Paper.Hypergraph
