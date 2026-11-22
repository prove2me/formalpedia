-- Prove2me | solution 1 for Paper.Hypergraph.full_integral_separator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:44.384799+00:00
-- url     : https://prove2.me/submissions/0f6ecf40-c206-43fa-a28b-ad2930cf7bdf

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
theorem _root_.solution (H : Hypergraph) (γ : ℕ → ℝ) (η : ℝ) :
    H.IntegralBalanced γ η H.vertices := by
  refine ⟨Subset.refl _, ?_⟩
  intro K hK
  simp [components, induce] at hK
  rcases hK with ⟨rfl, v, hv⟩
  simp at hv
end Paper.Hypergraph
