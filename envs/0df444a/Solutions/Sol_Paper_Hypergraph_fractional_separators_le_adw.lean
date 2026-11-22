-- Prove2me | solution 1 for Paper.Hypergraph.fractional_separators_le_adw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:33.734512+00:00
-- url     : https://prove2.me/submissions/d1b48699-165e-4cd9-af98-c0585128f713

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_elementary_width_bounds
import Theorems.Thm_Paper_Hypergraph_width_hereditary
import Theorems.Thm_Paper_Hypergraph_beta_le_adw

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {θ : ℝ}
    (hθ : 1 / 2 ≤ θ ∧ θ < 1) : H.fsep θ ≤ H.adw := by
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro r (rfl | ⟨W, hW, γ, hγ, rfl⟩)
  · exact H.elementary_width_bounds.1
  · exact ((H.induce W).beta_le_adw hγ hθ).trans (H.width_hereditary W).1
end Paper.Hypergraph
