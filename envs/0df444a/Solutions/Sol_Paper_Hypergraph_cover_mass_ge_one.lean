-- Prove2me | solution 1 for Paper.Hypergraph.cover_mass_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:06.719869+00:00
-- url     : https://prove2.me/submissions/90565652-6acd-4134-88a4-e13e045d69c5

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
theorem _root_.solution (H : Hypergraph) {Z : Finset ℕ} {γ : ℕ → ℝ}
    (hZ : Z ⊆ H.vertices) (hne : Z.Nonempty) (hγ : H.Cover (indicator Z) γ) :
    1 ≤ ∑ e ∈ H.edges, γ e := by
  obtain ⟨v, hv⟩ := hne
  have hh := hγ.2 v (hZ hv)
  simp only [indicator, if_pos hv] at hh
  exact hh.trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun e he _ => hγ.1 e he))
end Paper.Hypergraph
