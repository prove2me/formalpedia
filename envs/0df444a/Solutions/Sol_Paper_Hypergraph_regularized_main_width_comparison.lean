-- Prove2me | solution 1 for Paper.Hypergraph.regularized_main_width_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:44.897421+00:00
-- url     : https://prove2.me/submissions/de412adf-8d8b-4fe8-abe5-49169af699f8

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_elementary_width_bounds
import Theorems.Thm_Paper_Hypergraph_componentFactor_ge_one
import Theorems.Thm_Paper_Hypergraph_width_hereditary
import Theorems.Thm_Paper_Hypergraph_component_connected
import Theorems.Thm_Paper_Hypergraph_component_factor_le_componentFactor
import Theorems.Thm_Paper_Hypergraph_component_reduction
import Theorems.Thm_Paper_Hypergraph_width_scale_mono
import Theorems.Thm_Paper_Hypergraph_connected_width_comparison

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (rounding : BalancedRounding) : ∃ C : ℝ, 0 < C ∧ ∀ H : Hypergraph,
    H.fhw ≤ C * H.componentFactor * (H.adw + 1) * Real.log (2 + H.adw) := by
  obtain ⟨C, hC, hconnected⟩ := connected_width_comparison rounding
  refine ⟨C, hC, ?_⟩
  intro H
  have ha := H.elementary_width_bounds.1
  have hl : 0 ≤ H.componentFactor := by have := H.componentFactor_ge_one; linarith
  have hlog : 0 ≤ Real.log (2 + H.adw) := Real.log_nonneg (by linarith)
  rw [H.component_reduction.1]
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro r (rfl | ⟨K, hK, rfl⟩)
  · positivity
  · have hak := (H.induce K).elementary_width_bounds.1
    have hscale := width_scale_mono hak (H.width_hereditary K).1
    have hfactor := H.component_factor_le_componentFactor hK
    calc
      (H.induce K).fhw ≤ C * (H.induce K).structuralFactor *
          (((H.induce K).adw + 1) * Real.log (2 + (H.induce K).adw)) := by
        convert hconnected (H.induce K) (H.component_connected hK) using 1 <;> ring
      _ ≤ C * H.componentFactor * ((H.adw + 1) * Real.log (2 + H.adw)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hfactor hC.le) hscale
          (mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) (mul_nonneg hC.le hl)
      _ = _ := by ring
end Paper.Hypergraph
