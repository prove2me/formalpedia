-- Prove2me | solution 1 for Paper.Hypergraph.rounding_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:25.714373+00:00
-- url     : https://prove2.me/submissions/57d66e31-7f56-4721-94aa-fedf774fab5d

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
theorem _root_.solution {q : ℝ} (hq : 0 ≤ q) :
    ((44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
      (1 - (1 / 2 : ℝ))) * q ≤
      (120 / Real.log 2) * (q + 1) * Real.log (2 + q) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 0 < Real.log (2 + q) := Real.log_pos (by linarith)
  have hlow : Real.log 2 ≤ Real.log (2 + q) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog : Real.log (q / (1 - (1 / 2 : ℝ))) ≤
      Real.log 2 + Real.log (2 + q) := by
    by_cases hq0 : q = 0
    · simp only [hq0, zero_div, Real.log_zero, add_zero]
      positivity
    · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
      calc
        Real.log (q / (1 - (1 / 2 : ℝ))) ≤ Real.log (2 * (2 + q)) :=
          Real.log_le_log (by positivity) (by norm_num; linarith)
        _ = _ := Real.log_mul (by norm_num) (by linarith)
  have hb : (44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
      (1 - (1 / 2 : ℝ)) ≤ (120 / Real.log 2) * Real.log (2 + q) := by
    norm_num at hlog ⊢
    field_simp at hlog ⊢
    nlinarith
  calc
    _ ≤ ((120 / Real.log 2) * Real.log (2 + q)) * q := mul_le_mul_of_nonneg_right hb hq
    _ ≤ ((120 / Real.log 2) * Real.log (2 + q)) * (q + 1) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      positivity
    _ = _ := by ring
end Paper.Hypergraph
