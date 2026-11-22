-- Prove2me | solution 1 for Paper.Hypergraph.trimDemand_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:21.685423+00:00
-- url     : https://prove2.me/submissions/3c3a32bd-c027-4764-b0d8-889ad84a631a

import Definitions.Def_Paper_RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Paper_RoundingIndependence

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (x : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    H.vertices.filter (fun v => trimDemand x ε v ≠ 0) ⊆ H.vertices.filter (fun v => x v ≠ 0) := by
  intro v hv
  obtain ⟨hv, hz⟩ := mem_filter.mp hv
  refine mem_filter.mpr ⟨hv, ?_⟩
  intro h0
  simp [trimDemand, h0, not_le.mpr hε] at hz
end Paper.Hypergraph
