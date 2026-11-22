-- Prove2me | solution 1 for Paper.Hypergraph.beta_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:56.039511+00:00
-- url     : https://prove2.me/submissions/15355184-12b6-4562-840f-1f8d03770595

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_full_fractional_separator

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ : ℕ → ℝ} (hγ : H.EdgeWeight γ)
    {θ : ℝ} (hθ : 0 < θ ∧ θ < 1) : 0 ≤ H.beta θ γ ∧ H.beta θ γ ≤ H.edges.card := by
  have hlo : ∀ r ∈ {r | ∃ x, H.FractionalBalanced γ θ x ∧ r = H.coverCost x}, 0 ≤ r := by
    rintro r ⟨x, hx, rfl⟩
    exact H.coverCost_nonneg x
  have hfull := H.full_fractional_separator hγ hθ
  refine ⟨Real.sInf_nonneg hlo, ?_⟩
  exact (csInf_le ⟨0, hlo⟩ ⟨indicator H.vertices, hfull.1, rfl⟩).trans hfull.2
end Paper.Hypergraph
