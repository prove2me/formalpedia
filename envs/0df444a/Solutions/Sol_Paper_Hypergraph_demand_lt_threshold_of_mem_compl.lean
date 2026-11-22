-- Prove2me | solution 1 for Paper.Hypergraph.demand_lt_threshold_of_mem_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:03.061958+00:00
-- url     : https://prove2.me/submissions/4422b656-f5f8-4926-beae-8c5c8a34a80f

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (x : ℕ → ℝ)
    (a : ℝ) {v : ℕ} (hv : v ∈ H.vertices \ H.roundingThreshold x a) : x v < a := by
  obtain ⟨hv, hn⟩ := mem_sdiff.mp hv
  exact lt_of_not_ge fun h => hn (mem_filter.mpr ⟨hv, h⟩)
end Paper.Hypergraph
