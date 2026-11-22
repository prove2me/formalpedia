-- Prove2me | solution 1 for Paper.Hypergraph.independenceNumber_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:40.396279+00:00
-- url     : https://prove2.me/submissions/f50a845a-b862-4a2c-90e8-555a40b43727

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
theorem _root_.solution (H : Hypergraph) (hne : H.vertices.Nonempty) :
    1 ≤ H.independenceNumber := by
  obtain ⟨v, hv⟩ := hne
  have hmem : {v} ∈ H.vertices.powerset.filter H.independent := by
    simp [independent, hv]
  have hh := Finset.le_sup (f := Finset.card) hmem
  simpa [independenceNumber] using hh
end Paper.Hypergraph
