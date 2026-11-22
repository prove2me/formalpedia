-- Prove2me | solution 1 for Paper.Hypergraph.full_fractional_separator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:09.733637+00:00
-- url     : https://prove2.me/submissions/1cfd62a3-9135-4b80-b1aa-ad9c50dba4f1

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_indicator_equivalence

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : H.EdgeWeight γ) {θ : ℝ} (hθ : 0 < θ ∧ θ < 1) :
    H.FractionalBalanced γ θ (indicator H.vertices) ∧
      H.coverCost (indicator H.vertices) ≤ H.edges.card := by
  constructor
  · apply (H.indicator_equivalence hγ hθ (Subset.refl _)).mpr
    refine ⟨Subset.refl _, ?_⟩
    intro K hK
    simp [components, induce] at hK
    rcases hK with ⟨rfl, v, hv⟩
    simp at hv
  · have hcover : H.Cover (indicator H.vertices) (fun _ => 1) := by
      refine ⟨by simp, ?_⟩
      intro v hv
      obtain ⟨e, he, hve⟩ := H.no_isolated v hv
      simp only [indicator, if_pos hv]
      exact single_le_sum (f := fun _ : ℕ => (1 : ℝ))
        (s := H.edges.filter (fun e => v ∈ H.edge e)) (fun _ _ => zero_le_one)
        (mem_filter.mpr ⟨he, hve⟩)
    simpa using H.coverCost_le hcover
end Paper.Hypergraph
