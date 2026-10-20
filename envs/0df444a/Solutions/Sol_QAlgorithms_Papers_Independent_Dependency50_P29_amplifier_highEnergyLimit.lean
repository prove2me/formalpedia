-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P29.amplifier_highEnergyLimit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:43:49.000891+00:00
-- url     : https://prove2.me/submissions/5eb213eb-4202-4d39-a538-cb8ebfd1e9d7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P29

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P29

open Filter

-- PDF p.2, Eq.(2): reuse the accepted entropy in bits; its complete body
-- implements the same zero-occupation convention as this paper.

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

lemma g52a_te_eq (x : ℝ) (hx : 0 < x) :
    thermalEntropy x * Real.log 2 = Real.log (x + 1) + x * Real.log (1 + 1 / x) := by
  have hl2 : Real.log 2 ≠ 0 := by positivity
  unfold thermalEntropy
  rw [div_mul_cancel₀ _ hl2]
  have : 1 + 1 / x = (x + 1) / x := by field_simp
  rw [this, Real.log_div (by linarith) hx.ne']
  ring

lemma g52a_h_tendsto {f : ℝ → ℝ} (hf : Tendsto f atTop atTop) :
    Tendsto (fun N => f N * Real.log (1 + 1 / f N)) atTop (nhds 1) :=
  (Real.tendsto_mul_log_one_add_div_atTop 1).comp hf

/-- PDF p.24, Eq.(334): high-energy limit of Eq.(333), including its identity endpoint.
The finite formula is asserted for `gain > 1`; at `gain = 1` the limit is positive infinity.
This records the limit of the displayed expression, with provenance [27,29,30],
and does not define or identify an unconstrained operational capacity. -/
theorem solution :
    (∀ gain : ℝ, 1 < gain →
      Tendsto (amplifierFormula gain) atTop
        (nhds (Real.log (gain / (gain - 1)) / Real.log 2))) ∧
    Tendsto (amplifierFormula 1) atTop atTop := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro G hG
    have hG1 : 0 < G - 1 := by linarith
    have ha : Tendsto (fun N : ℝ => G * N + G - 1) atTop atTop := by
      apply tendsto_atTop_add_const_right
      exact tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (by linarith))
    have hb : Tendsto (fun N : ℝ => (G - 1) * (N + 1)) atTop atTop :=
      (tendsto_atTop_add_const_right _ _ tendsto_id).const_mul_atTop hG1
    have hr : Tendsto (fun N : ℝ => G / ((G - 1) + 1 / (N + 1))) atTop (nhds (G / (G - 1))) := by
      apply Tendsto.div tendsto_const_nhds _ hG1.ne'
      have : Tendsto (fun N : ℝ => 1 / (N + 1)) atTop (nhds 0) := by
        simp only [one_div]
        exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
      simpa using this.const_add (G - 1)
    have hlog := (hr.log (div_pos (by linarith) hG1).ne')
    have hsum := ((hlog.add ((g52a_h_tendsto ha).sub (g52a_h_tendsto hb))).div_const
      (Real.log 2))
    simp only [sub_self, add_zero] at hsum
    apply hsum.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    have hapos : 0 < G * N + G - 1 := by nlinarith
    have hbpos : 0 < (G - 1) * (N + 1) := by positivity
    unfold amplifierFormula
    symm
    rw [eq_div_iff hl2.ne', sub_mul, g52a_te_eq _ hapos, g52a_te_eq _ hbpos]
    have e1 : G * N + G - 1 + 1 = G * (N + 1) := by ring
    have e2 : G / ((G - 1) + 1 / (N + 1)) = (G * (N + 1)) / ((G - 1) * (N + 1) + 1) := by
      field_simp
    rw [e1, e2, Real.log_div (by positivity) (by positivity)]
    ring
  · have hN : Tendsto (fun N : ℝ => Real.log (N + 1) / Real.log 2) atTop atTop :=
      (Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_id)).atTop_div_const hl2
    apply tendsto_atTop_mono' _ _ hN
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN0
    have h0 : thermalEntropy 0 = 0 := by simp [thermalEntropy]
    have hval : amplifierFormula 1 N = thermalEntropy N := by
      unfold amplifierFormula
      have : (1 - 1) * (N + 1) = 0 := by ring
      rw [this, h0, one_mul, add_sub_cancel_right, sub_zero]
    rw [hval, div_le_iff₀ hl2, g52a_te_eq _ hN0]
    have : 0 ≤ N * Real.log (1 + 1 / N) :=
      mul_nonneg hN0.le (Real.log_nonneg (by have := one_div_pos.mpr hN0; linarith))
    linarith


end

