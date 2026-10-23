-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P24.pureLoss_highEnergyLimit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:02:28.716547+00:00
-- url     : https://prove2.me/submissions/08c4f577-3a0d-4792-8a28-3584e4ef28fe

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P24

namespace X6P24

open Filter QAlgorithms.Papers.Independent.Frontier30.P24

/-- `(x+1) log(x+1) - x log x - log x → 1`. -/
lemma h_tendsto : Tendsto (fun x : ℝ => (x + 1) * Real.log (x + 1) - x * Real.log x - Real.log x)
    atTop (nhds 1) := by
  have h1 := Real.tendsto_mul_log_one_add_div_atTop 1
  have h2 : Tendsto (fun x : ℝ => Real.log (1 + 1 / x)) atTop (nhds 0) := by
    have : Tendsto (fun x : ℝ => 1 + 1 / x) atTop (nhds 1) := by
      have := (tendsto_const_nhds (x := (1:ℝ))).add
        ((tendsto_const_nhds (x := (1:ℝ))).div_atTop tendsto_id)
      simpa using this
    have := ((Real.continuousAt_log one_ne_zero).tendsto).comp this
    simpa [Function.comp_def] using this
  have := h1.add h2
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have e : 1 + 1 / x = (x + 1) / x := by field_simp
  rw [e, Real.log_div (by linarith) hx.ne']
  ring

lemma diff_tendsto (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℝ => ((a * N + 1) * Real.log (a * N + 1) - a * N * Real.log (a * N)) -
      ((b * N + 1) * Real.log (b * N + 1) - b * N * Real.log (b * N))) atTop
      (nhds (Real.log (a / b))) := by
  have ta : Tendsto (fun N : ℝ => a * N) atTop atTop := tendsto_id.const_mul_atTop ha
  have tb : Tendsto (fun N : ℝ => b * N) atTop atTop := tendsto_id.const_mul_atTop hb
  have := ((h_tendsto.comp ta).sub (h_tendsto.comp tb)).add_const (Real.log (a / b))
  rw [sub_self, zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  simp only [Function.comp]
  rw [Real.log_div ha.ne' hb.ne', Real.log_mul ha.ne' hN.ne', Real.log_mul hb.ne' hN.ne']
  ring

end X6P24

open Filter QAlgorithms.Papers.Independent.Frontier30.P24 X6P24

theorem solution :
    (∀ eta : ℝ, 0 ≤ eta → eta < 1 →
      Tendsto (pureLossSymmetricBound eta) atTop
        (nhds (Real.log ((1 + eta) / (1 - eta)) / Real.log 2))) ∧
    Tendsto (pureLossSymmetricBound 1) atTop atTop := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨fun eta h0 h1 => ?_, ?_⟩
  · have := (diff_tendsto ((1 + eta) / 2) ((1 - eta) / 2) (by linarith) (by linarith)).div_const
      (Real.log 2)
    have e : (1 + eta) / 2 / ((1 - eta) / 2) = (1 + eta) / (1 - eta) := by
      field_simp
    rw [e] at this
    refine this.congr (fun N => ?_)
    simp only [pureLossSymmetricBound, bosonicEntropy]
    rw [sub_div]
    congr 2 <;> ring_nf
  · have := (h_tendsto.add_atTop Real.tendsto_log_atTop).atTop_div_const hl2
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [pureLossSymmetricBound, bosonicEntropy]
    norm_num
