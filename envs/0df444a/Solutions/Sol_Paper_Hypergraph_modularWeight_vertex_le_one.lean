-- Prove2me | solution 1 for Paper.Hypergraph.modularWeight_vertex_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:30.428573+00:00
-- url     : https://prove2.me/submissions/effdf399-c376-47b4-9de1-1ead979359be

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
theorem _root_.solution (H : Hypergraph) {w : ℕ → ℝ}
    (hw : H.ModularWeight w) {v : ℕ} (hv : v ∈ H.vertices) : w v ≤ 1 := by
  obtain ⟨e, he, hve⟩ := H.no_isolated v hv
  exact (single_le_sum (fun u _ => hw.1 u) hve).trans (hw.2 e he)
end Paper.Hypergraph
