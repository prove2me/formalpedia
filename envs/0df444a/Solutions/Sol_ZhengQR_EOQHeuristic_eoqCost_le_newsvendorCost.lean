-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.eoqCost_le_newsvendorCost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:34:38.937712+00:00
-- url     : https://prove2.me/submissions/e2ca2a2f-bb1b-4ed7-ac06-20490a2bae23

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel

open MeasureTheory ZhengQR.EOQHeuristic

/-- `h·t⁺ + p·(−t)⁺` written as a multiple of `|t|` plus a multiple of `t`. -/
private theorem pw_form (h p t : ℝ) :
    h * max t 0 + p * max (-t) 0 = ((h + p) / 2) * |t| + ((h - p) / 2) * t := by
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_left ht, max_eq_right (by linarith : -t ≤ 0), abs_of_nonneg ht]
    ring
  · rw [max_eq_right ht.le, max_eq_left (by linarith : (0:ℝ) ≤ -t), abs_of_neg ht]
    ring

theorem solution {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    ∀ y : ℝ, eoqCost lam L h p y ≤ newsvendorCost μ h p y := by
  intro y
  haveI : IsProbabilityMeasure μ := hM.isProb
  have hint : Integrable (fun x : ℝ => x) μ := hM.integrable
  have hlin : Integrable (fun x : ℝ => y - x) μ := (integrable_const y).sub hint
  have habs : Integrable (fun x : ℝ => |y - x|) μ := hlin.abs
  have hhp : 0 ≤ (h + p) / 2 := by
    have := hM.h_pos; have := hM.p_pos; linarith
  -- rewrite the integrand
  have hrw : ∀ x : ℝ, h * max (y - x) 0 + p * max (x - y) 0
      = ((h + p) / 2) * |y - x| + ((h - p) / 2) * (y - x) := by
    intro x
    have hneg : x - y = -(y - x) := by ring
    rw [hneg]
    exact pw_form h p (y - x)
  have hNV : newsvendorCost μ h p y
      = ((h + p) / 2) * (∫ x, |y - x| ∂μ) + ((h - p) / 2) * (y - lam * L) := by
    rw [newsvendorCost]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hrw)]
    rw [MeasureTheory.integral_add (habs.const_mul _) (hlin.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_sub (integrable_const y) hint, hM.mean]
    simp
  have hmean : (∫ x, (y - x) ∂μ) = y - lam * L := by
    rw [MeasureTheory.integral_sub (integrable_const y) hint, hM.mean]
    simp
  have hjensen : |y - lam * L| ≤ ∫ x, |y - x| ∂μ := by
    rw [← hmean]
    exact MeasureTheory.abs_integral_le_integral_abs
  have hEOQ : eoqCost lam L h p y
      = ((h + p) / 2) * |y - lam * L| + ((h - p) / 2) * (y - lam * L) := by
    rw [eoqCost]
    have hneg : lam * L - y = -(y - lam * L) := by ring
    rw [hneg]
    exact pw_form h p (y - lam * L)
  rw [hEOQ, hNV]
  have := mul_le_mul_of_nonneg_left hjensen hhp
  linarith
