-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P29.pureLoss_highEnergyLimit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:43:41.815411+00:00
-- url     : https://prove2.me/submissions/ada0c3ae-dadc-4646-a7f0-bc57b4999f93

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P29

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P29

open Filter

-- PDF p.2, Eq.(2): reuse the accepted entropy in bits; its complete body
-- implements the same zero-occupation convention as this paper.

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

theorem g52b_te {x : ℝ} (hx : 0 < x) :
    thermalEntropy x = (Real.log (x + 1) + x * Real.log (1 + 1 / x)) / Real.log 2 := by
  unfold thermalEntropy
  have h : Real.log (1 + 1 / x) = Real.log (x + 1) - Real.log x := by
    rw [show (1:ℝ) + 1 / x = (x + 1) / x by field_simp,
      Real.log_div (by positivity) hx.ne']
  rw [h]; ring

theorem g52b_A : Tendsto (fun x : ℝ => x * Real.log (1 + 1 / x)) atTop (nhds 1) :=
  Real.tendsto_mul_log_one_add_div_atTop 1

/-- PDF p.24, Eq.(332): high-energy limit of Eq.(331), including its identity endpoint.
For `1/2 ≤ eta < 1` the limit is the stated finite base-two logarithm.
At `eta = 1` the formula is `g(occupation)` and diverges to positive infinity;
this is the extended-value reading of the printed singular logarithm, not real division by zero.
The paper relates this limit to [27]; no independent operational capacity formula is assumed. -/
theorem solution :
    (∀ eta : ℝ, (1 / 2 : ℝ) ≤ eta → eta < 1 →
      Tendsto (lossFormula eta) atTop
        (nhds (Real.log (eta / (1 - eta)) / Real.log 2))) ∧
    Tendsto (lossFormula 1) atTop atTop := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨fun eta h1 h2 => ?_, ?_⟩
  · have ha : 0 < eta := by linarith
    have hb : 0 < 1 - eta := by linarith
    have hinv := tendsto_inv_atTop_zero (𝕜 := ℝ)
    have hq : Tendsto (fun N : ℝ => (eta + N⁻¹) / ((1 - eta) + N⁻¹)) atTop
        (nhds ((eta + 0) / ((1 - eta) + 0))) :=
      (tendsto_const_nhds.add hinv).div (tendsto_const_nhds.add hinv) (by linarith)
    have hlog := hq.log (by
      rw [add_zero, add_zero]; exact (div_pos ha hb).ne')
    have hA1 := g52b_A.comp (tendsto_id.const_mul_atTop ha)
    have hA2 := g52b_A.comp (tendsto_id.const_mul_atTop hb)
    have hF := ((hlog.add hA1).sub hA2).div_const (Real.log 2)
    have hlim : (Real.log ((eta + 0) / ((1 - eta) + 0)) + 1 - 1) / Real.log 2 =
        Real.log (eta / (1 - eta)) / Real.log 2 := by
      rw [add_zero, add_zero]; ring
    rw [hlim] at hF
    refine hF.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with N hN
    simp only [Function.comp, id, lossFormula]
    rw [g52b_te (by positivity), g52b_te (by positivity)]
    have e : (eta + N⁻¹) / ((1 - eta) + N⁻¹) = (eta * N + 1) / ((1 - eta) * N + 1) := by
      field_simp
    rw [e, Real.log_div (by positivity) (by positivity)]
    ring
  · have hlog : Tendsto (fun N : ℝ => Real.log (N + 1) / Real.log 2) atTop atTop :=
      (Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)).atTop_div_const hl2
    refine tendsto_atTop_mono' _ ?_ hlog
    filter_upwards [eventually_gt_atTop (0:ℝ)] with N hN
    have h0 : thermalEntropy ((1 - 1) * N) = 0 := by simp [thermalEntropy]
    simp only [lossFormula, one_mul, h0, sub_zero]
    rw [g52b_te hN]
    apply div_le_div_of_nonneg_right _ hl2.le
    have : 0 ≤ N * Real.log (1 + 1 / N) :=
      mul_nonneg hN.le (Real.log_nonneg (by have := one_div_pos.mpr hN; linarith))
    linarith


end

