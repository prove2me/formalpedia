-- Prove2me | solution 1 for Paper.Hypergraph.sep_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:43.646167+00:00
-- url     : https://prove2.me/submissions/30fabb43-112e-497f-b167-205978334a51

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_integralOptimum_bounds

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {η : ℝ} (hη : 0 < η ∧ η < 1) :
    0 ≤ H.sep η ∧ H.sep η ≤ H.edges.card := by
  have hb : ∀ r ∈ insert 0 {r | ∃ W ⊆ H.vertices, ∃ γ,
      (H.induce W).EdgeWeight γ ∧ r = (H.induce W).integralOptimum η γ},
      r ≤ (H.edges.card : ℝ) := by
    rintro r (rfl | ⟨W, hW, γ, hγ, rfl⟩)
    · positivity
    · exact ((H.induce W).integralOptimum_bounds γ hγ hη).2.trans (by
        exact_mod_cast card_filter_le H.edges (fun e => (H.edge e ∩ W).Nonempty))
  exact ⟨le_csSup ⟨_, hb⟩ (Set.mem_insert 0 _), csSup_le ⟨0, Set.mem_insert 0 _⟩ hb⟩
end Paper.Hypergraph
