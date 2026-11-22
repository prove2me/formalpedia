-- Prove2me | solution 1 for Paper.Hypergraph.edgeVolume_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:51.557318+00:00
-- url     : https://prove2.me/submissions/2c68b91d-d5d0-481c-9379-3123289bd3db

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
theorem _root_.solution (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) {A B : Finset ℕ} (hAB : A ⊆ B) :
    H.edgeVolume γ A ≤ H.edgeVolume γ B := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨he, hm⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨he, fun hd => hm (hd.mono_right hAB)⟩
  · intro e he _
    exact hγ e (mem_filter.mp he).1
end Paper.Hypergraph
