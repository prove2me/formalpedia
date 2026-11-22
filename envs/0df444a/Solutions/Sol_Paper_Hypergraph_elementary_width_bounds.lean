-- Prove2me | solution 1 for Paper.Hypergraph.elementary_width_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:51.605333+00:00
-- url     : https://prove2.me/submissions/7a6c3f39-f96c-41d9-ac33-b19e7dd23002

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
theorem _root_.solution (H : Hypergraph) :
    0 ≤ H.adw ∧ H.adw ≤ H.vertices.card ∧ 0 ≤ H.fhw := by
  have hbound : ∀ r ∈ {r | ∃ w, H.ModularWeight w ∧
      r = H.optimalWidth (modularValue w)}, r ≤ (H.vertices.card : ℝ) := by
    rintro r ⟨w, hw, rfl⟩
    calc
      H.optimalWidth (modularValue w) ≤ modularValue w H.vertices :=
        (H.optimalWidth_bounds _ (fun S _ => sum_nonneg (fun v _ => hw.1 v))).2
      _ ≤ (H.vertices.card : ℝ) := by
        simpa [modularValue] using
          (sum_le_sum (fun v hv => H.modularWeight_vertex_le_one hw hv))
  have hzero : H.ModularWeight (fun _ => 0) := ⟨by simp, by simp⟩
  refine ⟨?_, csSup_le ⟨_, _, hzero, rfl⟩ hbound, ?_⟩
  · exact (H.optimalWidth_bounds (modularValue (fun _ => 0))
      (fun S _ => by simp [modularValue])).1.trans
        (le_csSup ⟨_, hbound⟩ ⟨_, hzero, rfl⟩)
  · exact (H.optimalWidth_bounds _ (fun S _ => H.coverCost_nonneg (indicator S))).1
end Paper.Hypergraph
