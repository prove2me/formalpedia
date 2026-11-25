-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.heis_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:19.837209+00:00
-- url     : https://prove2.me/submissions/25cdee3b-b166-44e1-8a80-7e515ec3c0a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_NHeisInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_A_heis_norm_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.S0 ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
theorem _root_.solution (m : ℕ) {d : ℝ} (hd : 0 ≤ d) (x : (Fin m → ℂ) × ℝ) :
    (1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2)) ≤
      (2 : ℝ) ^ (d / 2) * (1 + ‖x‖) ^ (-d) := by
  have hn := heis_norm_sq_le m x
  have hS : 0 ≤ ∑ i, Complex.normSq (x.1 i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  set Q := 1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2 with hQ
  have hQ0 : 0 < Q := by nlinarith [sq_nonneg x.2]
  have ha0 : 0 < 1 + ‖x‖ := by have := norm_nonneg x; linarith
  have hsq : (1 + ‖x‖) ^ 2 ≤ 2 * Q := by nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]
  have had : (1 + ‖x‖) ^ d ≤ (2 : ℝ) ^ (d / 2) * Q ^ (d / 2) := by
    have h1 : (1 + ‖x‖) ^ d = ((1 + ‖x‖) ^ (2 : ℝ)) ^ (d / 2) := by
      rw [← Real.rpow_mul ha0.le]; congr 1; ring
    rw [h1, ← Real.mul_rpow (by norm_num) hQ0.le]
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    rw [Real.rpow_two]; exact hsq
  have hQd : 0 < Q ^ (d / 2) := Real.rpow_pos_of_pos hQ0 _
  have had0 : 0 < (1 + ‖x‖) ^ d := Real.rpow_pos_of_pos ha0 _
  rw [Real.rpow_neg hQ0.le, Real.rpow_neg ha0.le, ← div_eq_mul_inv, le_div_iff₀ had0]
  calc (Q ^ (d / 2))⁻¹ * (1 + ‖x‖) ^ d ≤ (Q ^ (d / 2))⁻¹ * ((2 : ℝ) ^ (d / 2) * Q ^ (d / 2)) := by
        gcongr
    _ = (2 : ℝ) ^ (d / 2) := by
        rw [mul_comm ((2 : ℝ) ^ (d / 2)), ← mul_assoc, inv_mul_cancel₀ hQd.ne', one_mul]
end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
