-- Prove2me | solution 1 for Paper.Hypergraph.beta_le_fsep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:44.145834+00:00
-- url     : https://prove2.me/submissions/e0b608fe-d030-4d15-a5fb-45be1f34b167

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_beta_bounds

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {W : Finset ℕ} (hW : W ⊆ H.vertices)
    {γ : ℕ → ℝ} (hγ : (H.induce W).EdgeWeight γ) {θ : ℝ} (hθ : 0 < θ ∧ θ < 1) :
    (H.induce W).beta θ γ ≤ H.fsep θ := by
  refine le_csSup ?_ (Set.mem_insert_of_mem 0 ⟨W, hW, γ, hγ, rfl⟩)
  refine ⟨H.edges.card, ?_⟩
  rintro r (rfl | ⟨U, hU, δ, hδ, rfl⟩)
  · positivity
  · exact ((H.induce U).beta_bounds hδ hθ).2.trans (by
      exact_mod_cast (card_filter_le H.edges (fun e => (H.edge e ∩ U).Nonempty)))
end Paper.Hypergraph
