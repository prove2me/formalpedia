-- Prove2me | solution 1 for Paper.Hypergraph.cutoff_annulus_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:22.016409+00:00
-- url     : https://prove2.me/submissions/d5ade9b3-6668-40f0-9389-36498ec3536d

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
theorem _root_.solution {r L q : ℝ} (hr : 0 < r)
    (hD : 0 < 9 + 2 * L) (hq : q < (r / (9 + 2 * L)) / 2) :
    let δ := r / (9 + 2 * L)
    0 < δ - q ∧
      1 / (δ - q) ≤ (18 + 4 * L) / r ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ q → 0 ≤ u / (δ - q) ∧ u / (δ - q) < 1 := by
  dsimp
  have hδ : 0 < r / (9 + 2 * L) := div_pos hr hD
  have hgap : 0 < r / (9 + 2 * L) - q := by linarith
  refine ⟨hgap, ?_, ?_⟩
  · calc
      _ ≤ 2 / (r / (9 + 2 * L)) := (div_le_div_iff₀ hgap hδ).2 (by linarith)
      _ = _ := by field_simp; ring
  · intro u hu huq
    exact ⟨div_nonneg hu hgap.le, (div_lt_one hgap).2 (by linarith)⟩
end Paper.Hypergraph
