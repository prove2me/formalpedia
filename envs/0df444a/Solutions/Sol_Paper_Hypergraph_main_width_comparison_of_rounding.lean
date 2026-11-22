-- Prove2me | solution 1 for Paper.Hypergraph.main_width_comparison_of_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:33.363271+00:00
-- url     : https://prove2.me/submissions/ab43c720-1229-47fd-a317-0478fb607169

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_elementary_width_bounds
import Theorems.Thm_Paper_Hypergraph_regularized_main_width_comparison
import Theorems.Thm_Paper_Hypergraph_lambda_ge_one
import Theorems.Thm_Paper_Hypergraph_structuralFactor_le_lambda
import Theorems.Thm_Paper_Hypergraph_componentFactor_le_structuralFactor

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (rounding : BalancedRounding) : MainWidthComparison := by
  obtain ⟨C, hC, hmain⟩ := regularized_main_width_comparison rounding
  refine ⟨48 * C, by positivity, ?_⟩
  intro H hne
  have ha := H.elementary_width_bounds.1
  have hl : 0 ≤ H.lambda := le_trans (by norm_num) (H.lambda_ge_one hne)
  have hfactor := H.componentFactor_le_structuralFactor.trans (H.structuralFactor_le_lambda hne)
  have hb : H.fhw ≤ (4 * C) * H.lambda * ((H.adw + 1) * Real.log (2 + H.adw)) := by
    have hh := (hmain H).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor hC.le)
        (by linarith : 0 ≤ H.adw + 1)) (Real.log_nonneg (by linarith)))
    calc
      H.fhw ≤ C * (4 * H.lambda) * (H.adw + 1) * Real.log (2 + H.adw) := hh
      _ = _ := by ring
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  constructor
  · intro hlarge
    have hlog : 0 ≤ Real.log H.adw := Real.log_nonneg (by linarith)
    have hscale : (H.adw + 1) * Real.log (2 + H.adw) ≤
        4 * H.adw * (Real.log H.adw / Real.log 2) := by
      have hupper : Real.log (2 + H.adw) ≤ 2 * Real.log H.adw := by
        calc
          _ ≤ Real.log (H.adw * H.adw) := Real.log_le_log (by linarith) (by nlinarith)
          _ = _ := by rw [Real.log_mul (by linarith) (by linarith)]; ring
      have hdiv : Real.log H.adw ≤ Real.log H.adw / Real.log 2 := by
        apply (le_div_iff₀ h2).mpr
        nlinarith
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hdiv)]
    have hh := hb.trans (mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 4 * C * H.lambda))
    have hp : 0 ≤ C * H.lambda * H.adw * (Real.log H.adw / Real.log 2) := by positivity
    nlinarith
  · intro hsmall
    have hscale : (H.adw + 1) * Real.log (2 + H.adw) ≤ 9 := by
      have hh := Real.log_le_sub_one_of_pos (by linarith : 0 < 2 + H.adw)
      have hn : 0 ≤ Real.log (2 + H.adw) := Real.log_nonneg (by linarith)
      nlinarith
    have hh := hb.trans (mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 4 * C * H.lambda))
    nlinarith [mul_nonneg hC.le hl]
end Paper.Hypergraph
