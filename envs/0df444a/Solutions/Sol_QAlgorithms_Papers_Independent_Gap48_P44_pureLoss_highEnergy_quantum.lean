-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P44.pureLoss_highEnergy_quantum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T05:58:13.89543+00:00
-- url     : https://prove2.me/submissions/2f7b7f5a-6408-44b4-a530-17c8506260c5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P44
open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

theorem g78b_gte {x : ℝ} (hx : 0 < x) :
    g x = Real.log (x + 1) + x * Real.log (1 + 1 / x) := by
  unfold g
  have h : Real.log (1 + 1 / x) = Real.log (x + 1) - Real.log x := by
    rw [show (1:ℝ) + 1 / x = (x + 1) / x by field_simp,
      Real.log_div (by positivity) hx.ne']
  rw [h]; ring

theorem g78b_lim (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun G : ℝ => g (a * G) - g (b * G)) atTop
      (nhds (Real.log a - Real.log b)) := by
  have t1 : Tendsto (fun G : ℝ => a * G) atTop atTop := tendsto_id.const_mul_atTop ha
  have t2 : Tendsto (fun G : ℝ => b * G) atTop atTop := tendsto_id.const_mul_atTop hb
  have hA1 := (Real.tendsto_mul_log_one_add_div_atTop 1).comp t1
  have hA2 := (Real.tendsto_mul_log_one_add_div_atTop 1).comp t2
  have hinv := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have hq : Tendsto (fun G : ℝ => (a + G⁻¹) / (b + G⁻¹)) atTop
      (nhds ((a + 0) / (b + 0))) :=
    (tendsto_const_nhds.add hinv).div (tendsto_const_nhds.add hinv) (by simp; linarith)
  have hlog := hq.log (by simp; exact ⟨ha.ne', hb.ne'⟩)
  have hF := (hlog.add hA1).sub hA2
  have hlim : Real.log ((a + 0) / (b + 0)) + 1 - 1 = Real.log a - Real.log b := by
    simp [Real.log_div ha.ne' hb.ne']
  rw [hlim] at hF
  refine hF.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with G hG
  have h1 : 0 < a * G := by positivity
  have h2 : 0 < b * G := by positivity
  simp only [Function.comp]
  rw [g78b_gte h1, g78b_gte h2]
  have hG' : G ≠ 0 := hG.ne'
  have e : (a + G⁻¹) / (b + G⁻¹) = (a * G + 1) / (b * G + 1) := by
    rw [show a + G⁻¹ = (a * G + 1) / G by field_simp,
      show b + G⁻¹ = (b * G + 1) / G by field_simp,
      div_div_div_cancel_right₀ hG']
  rw [e, Real.log_div (by linarith) (by linarith)]
  ring

theorem g78b_ge_log {v : ℝ} (hv : 0 ≤ v) : Real.log (v + 1) ≤ g v := by
  unfold g
  have hl : Real.log v ≤ Real.log (v + 1) := by
    rcases hv.eq_or_lt with h | h
    · subst h; simp
    · exact Real.log_le_log h (by linarith)
  nlinarith

theorem g78b_atTop (a : ℝ) (ha : 0 < a) : Tendsto (fun G : ℝ => g (a * G)) atTop atTop := by
  have t1 : Tendsto (fun G : ℝ => a * G) atTop atTop := tendsto_id.const_mul_atTop ha
  have hl : Tendsto (fun G : ℝ => Real.log (a * G + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 t1)
  refine tendsto_atTop_mono' _ ?_ hl
  filter_upwards [eventually_gt_atTop (0:ℝ)] with G hG
  exact g78b_ge_log (by positivity)

/-- PDF p.7, (44): finite high-energy quantum-rate limit in nats.
The identity endpoint is excluded because the printed logarithm is singular. -/
theorem solution (eta : ℝ)
    (heta0 : (1 / 2 : ℝ) ≤ eta) (heta1 : eta < 1) :
    Tendsto (fun budget : ℝ => g (eta * budget) - g ((1 - eta) * budget))
      atTop (nhds (Real.log eta - Real.log (1 - eta))) := by
  have := g78b_lim eta (1 - eta) (by linarith) (by linarith)
  exact this


end
