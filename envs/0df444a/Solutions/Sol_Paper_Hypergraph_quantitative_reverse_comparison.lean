-- Prove2me | solution 1 for Paper.Hypergraph.quantitative_reverse_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:32.791161+00:00
-- url     : https://prove2.me/submissions/1efef34f-ccad-4615-8c20-d63ab18c28c3

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_width_hierarchy
import Theorems.Thm_Paper_Hypergraph_elementary_width_bounds
import Theorems.Thm_Paper_Hypergraph_componentFactor_ge_one
import Theorems.Thm_Paper_Hypergraph_regularized_main_width_comparison

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (rounding : BalancedRounding) : ∃ c : ℝ, 0 < c ∧ ∀ H : Hypergraph,
    H.adw + 1 ≤ H.subw + 1 ∧
    c * (H.fhw / (H.componentFactor * Real.log (2 + H.fhw))) ≤ H.adw + 1 := by
  obtain ⟨C, hC, hmain⟩ := regularized_main_width_comparison rounding
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro H
  have hh := H.width_hierarchy
  have ha := H.elementary_width_bounds.1
  have hf := H.elementary_width_bounds.2.2
  have hl : 0 < H.componentFactor := lt_of_lt_of_le (by norm_num) H.componentFactor_ge_one
  have hlog : 0 < Real.log (2 + H.fhw) := Real.log_pos (by linarith)
  have hlogs : Real.log (2 + H.adw) ≤ Real.log (2 + H.fhw) :=
    Real.log_le_log (by linarith) (by linarith [hh.1.trans hh.2])
  have hm : H.fhw ≤ C * H.componentFactor * (H.adw + 1) * Real.log (2 + H.fhw) :=
    (hmain H).trans (mul_le_mul_of_nonneg_left hlogs (by positivity))
  refine ⟨by linarith [hh.1], ?_⟩
  calc
    C⁻¹ * (H.fhw / (H.componentFactor * Real.log (2 + H.fhw))) =
        H.fhw / (C * (H.componentFactor * Real.log (2 + H.fhw))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ H.adw + 1 := (div_le_iff₀ (mul_pos hC (mul_pos hl hlog))).mpr (by nlinarith [hm])
end Paper.Hypergraph
