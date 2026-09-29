-- Prove2me | solution 1 for ZhengQR.CostBounds.eoq_invcost_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:34:39.618857+00:00
-- url     : https://prove2.me/submissions/8fa83bd0-fb03-42f6-898f-3c2c8a1995cd

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

open MeasureTheory ZhengQR.CostBounds

/-- `h·t⁺ + p·(−t)⁺` written as a multiple of `|t|` plus a multiple of `t`. -/
private theorem pw_form (h p t : ℝ) :
    h * max t 0 + p * max (-t) 0 = ((h + p) / 2) * |t| + ((h - p) / 2) * t := by
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_left ht, max_eq_right (by linarith : -t ≤ 0), abs_of_nonneg ht]
    ring
  · rw [max_eq_right ht.le, max_eq_left (by linarith : (0:ℝ) ≤ -t), abs_of_neg ht]
    ring

theorem solution (M : QRModel) : ∀ y : ℝ, M.Gd y ≤ M.G y := by
  intro y
  haveI : IsProbabilityMeasure M.μ := M.isProb
  have hint : Integrable (fun x : ℝ => x) M.μ := M.integrable_id
  have hlin : Integrable (fun x : ℝ => y - x) M.μ := (integrable_const y).sub hint
  have habs : Integrable (fun x : ℝ => |y - x|) M.μ := hlin.abs
  have hhp : 0 ≤ (M.h + M.p) / 2 := by
    have := M.h_pos; have := M.p_pos; linarith
  have hrw : ∀ x : ℝ, M.h * max (y - x) 0 + M.p * max (x - y) 0
      = ((M.h + M.p) / 2) * |y - x| + ((M.h - M.p) / 2) * (y - x) := by
    intro x
    have hneg : x - y = -(y - x) := by ring
    rw [hneg]
    exact pw_form M.h M.p (y - x)
  have hmean : (∫ x, (y - x) ∂M.μ) = y - M.lam * M.L := by
    rw [MeasureTheory.integral_sub (integrable_const y) hint, M.mean_eq]
    simp
  have hG : M.G y
      = ((M.h + M.p) / 2) * (∫ x, |y - x| ∂M.μ) + ((M.h - M.p) / 2) * (y - M.lam * M.L) := by
    rw [QRModel.G, newsvendorCost]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hrw)]
    rw [MeasureTheory.integral_add (habs.const_mul _) (hlin.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hmean]
  have hjensen : |y - M.lam * M.L| ≤ ∫ x, |y - x| ∂M.μ := by
    rw [← hmean]
    exact MeasureTheory.abs_integral_le_integral_abs
  have hGd : M.Gd y
      = ((M.h + M.p) / 2) * |y - M.lam * M.L| + ((M.h - M.p) / 2) * (y - M.lam * M.L) := by
    rw [QRModel.Gd, eoqInvCost]
    have hneg : M.lam * M.L - y = -(y - M.lam * M.L) := by ring
    rw [hneg]
    exact pw_form M.h M.p (y - M.lam * M.L)
  rw [hGd, hG]
  have := mul_le_mul_of_nonneg_left hjensen hhp
  linarith
