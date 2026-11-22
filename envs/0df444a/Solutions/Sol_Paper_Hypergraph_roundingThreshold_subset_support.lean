-- Prove2me | solution 1 for Paper.Hypergraph.roundingThreshold_subset_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:39.022081+00:00
-- url     : https://prove2.me/submissions/bcd499f6-25b3-4e48-b366-8c2810ec45f8

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
    {a : ℝ} (ha : 0 < a) :
    H.roundingThreshold x a ⊆ H.vertices.filter (fun v => x v ≠ 0) := by
  intro v hv
  obtain ⟨hv, hax⟩ := mem_filter.mp hv
  exact mem_filter.mpr ⟨hv, (ha.trans_le hax).ne'⟩
end Paper.Hypergraph
