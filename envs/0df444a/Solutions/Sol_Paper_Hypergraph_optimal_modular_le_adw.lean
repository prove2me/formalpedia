-- Prove2me | solution 1 for Paper.Hypergraph.optimal_modular_le_adw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:02.589812+00:00
-- url     : https://prove2.me/submissions/7375b1f4-d2ec-43ec-8c9d-1eb0fb98e4da

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_optimalWidth_bounds
import Theorems.Thm_Paper_Hypergraph_modularWeight_vertex_le_one

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {w : ℕ → ℝ} (hw : H.ModularWeight w) :
    H.optimalWidth (modularValue w) ≤ H.adw := by
  refine le_csSup ?_ ⟨w, hw, rfl⟩
  refine ⟨H.vertices.card, ?_⟩
  rintro r ⟨w', hw', rfl⟩
  calc
    H.optimalWidth (modularValue w') ≤ modularValue w' H.vertices :=
      (H.optimalWidth_bounds _ (fun S _ => sum_nonneg (fun u _ => hw'.1 u))).2
    _ ≤ (H.vertices.card : ℝ) := by
      simpa [modularValue] using
        (sum_le_sum (fun u hu => H.modularWeight_vertex_le_one hw' hu))
end Paper.Hypergraph
