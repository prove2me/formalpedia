-- Prove2me | solution 1 for Paper.Hypergraph.integralOptimum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:56.462295+00:00
-- url     : https://prove2.me/submissions/a5fe533f-9505-485b-8f45-2f2413c7c631

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_full_fractional_separator
import Theorems.Thm_Paper_Hypergraph_full_integral_separator

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (γ : ℕ → ℝ) {η : ℝ}
    (hγ : H.EdgeWeight γ) (hη : 0 < η ∧ η < 1) :
    0 ≤ H.integralOptimum η γ ∧ H.integralOptimum η γ ≤ H.edges.card := by
  have hn : ∀ r ∈ {r | ∃ S, H.IntegralBalanced γ η S ∧ r = H.setCoverCost S}, 0 ≤ r := by
    rintro r ⟨S, _, rfl⟩; exact H.coverCost_nonneg _
  constructor
  · exact le_csInf ⟨_, H.vertices, H.full_integral_separator γ η, rfl⟩ hn
  · exact (csInf_le ⟨0, hn⟩ ⟨H.vertices, H.full_integral_separator γ η, rfl⟩).trans
      (H.full_fractional_separator hγ hη).2
end Paper.Hypergraph
