-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P15.twisted_plob_improvement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:44:20.422544+00:00
-- url     : https://prove2.me/submissions/2ed8276f-05c5-4d31-8762-1db879516129

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P15
noncomputable section

open Filter

open scoped BigOperators ENNReal Topology Matrix

open QAlgorithms.Papers.Independent.Bridge50.P15
open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

theorem s110tp_cont : Continuous thermalEntropyBits := by
  have : thermalEntropyBits = fun N : ℝ =>
      ((1 + N) * Real.log (1 + N) - N * Real.log N) / Real.log 2 := by
    funext N; unfold thermalEntropyBits Real.logb; ring
  rw [this]
  exact ((Real.continuous_mul_log.comp (continuous_const.add continuous_id)).sub
    Real.continuous_mul_log).div_const _

theorem s110tp_tw (eta N : ℝ) (heta : 0 < eta) (heta1 : eta < 1)
    (hN : 0 ≤ N) (hprime : 0 < eta - N * (1 - eta)) :
    twistedBound eta N ≤ max 0 (Real.logb 2 (eta / (1 - eta))) := by
  have hA : 0 < 1 - eta := by linarith
  have hB : 0 < 1 + N := by linarith
  have hpos : 0 < (eta - N * (1 - eta)) / ((1 + N) * (1 - eta)) := by positivity
  have key : (eta - N * (1 - eta)) / ((1 + N) * (1 - eta)) ≤ eta / (1 - eta) := by
    rw [div_le_div_iff₀ (by positivity) hA]
    nlinarith [mul_pos hA hA, mul_nonneg hN hA.le, mul_nonneg (mul_nonneg hN hA.le) hA.le]
  unfold twistedBound
  exact max_le_max le_rfl (Real.logb_le_logb_of_le (by norm_num) hpos key)

theorem s110tp_f (eta N : ℝ) (hN : 0 ≤ N) (heta : N / (N + 1) < eta) (heta1 : eta < 1) :
    0 < -Real.logb 2 (1 - eta) - N * Real.logb 2 eta - thermalEntropyBits N := by
  have hB : 0 < N + 1 := by linarith
  have hA : 0 < 1 - eta := by linarith
  have he : 0 < eta := lt_of_le_of_lt (by positivity) heta
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold thermalEntropyBits Real.logb
  -- reduce to: (1-eta)... via log t ≤ t - 1
  have h1 : Real.log ((1 - eta) * (N + 1)) ≤ (1 - eta) * (N + 1) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rcases hN.lt_or_eq with hNp | hN0
  · have hne : eta * (N + 1) / N ≠ 1 := by
      intro h; rw [div_eq_one_iff_eq hNp.ne'] at h
      rw [div_lt_iff₀ hB] at heta; linarith
    have h2 : Real.log (eta * (N + 1) / N) < eta * (N + 1) / N - 1 :=
      Real.log_lt_sub_one_of_pos (by positivity) hne
    rw [Real.log_mul hA.ne' hB.ne'] at h1
    rw [Real.log_div (by positivity) hNp.ne', Real.log_mul he.ne' hB.ne'] at h2
    have h2' : N * (Real.log eta + Real.log (N + 1) - Real.log N) < eta * (N + 1) - N := by
      have := mul_lt_mul_of_pos_left h2 hNp
      have e : N * (eta * (N + 1) / N - 1) = eta * (N + 1) - N := by field_simp
      rw [e] at this; exact this
    rw [show (1 + N) = N + 1 by ring]
    have : 0 < -Real.log (1 - eta) - N * Real.log eta - ((N + 1) * Real.log (N + 1) - N * Real.log N) := by
      nlinarith
    have := div_pos this hl2
    refine lt_of_lt_of_eq this ?_
    ring
  · subst hN0
    have : Real.log (1 - eta) < 0 := Real.log_neg hA (by linarith)
    simp
    exact div_neg_of_neg_of_pos this hl2

theorem solution :
    (∀ eta : ℝ, 0 < eta → eta < 1 → ∃ delta : ℝ, 0 < delta ∧
      ∀ N : ℝ, 0 ≤ N → N < delta → 0 < eta - N * (1 - eta) →
        twistedBound eta N < plobBound eta N) ∧
    (∀ N : ℝ, 0 ≤ N → ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ eta : ℝ, N / (N + 1) < eta → eta < N / (N + 1) + epsilon → eta < 1 →
        0 < eta - N * (1 - eta) ∧ twistedBound eta N < plobBound eta N) := by
  constructor
  · intro eta he he1
    have hA : 0 < 1 - eta := by linarith
    set T0 := max 0 (Real.logb 2 (eta / (1 - eta)))
    set g : ℝ → ℝ := fun N => -Real.logb 2 (1 - eta) - N * Real.logb 2 eta - thermalEntropyBits N
    have hg : Continuous g := by
      exact (continuous_const.sub (continuous_id.mul continuous_const)).sub s110tp_cont
    have hT : T0 < g 0 := by
      have h0 : thermalEntropyBits 0 = 0 := by simp [thermalEntropyBits]
      have hl1 : Real.logb 2 (1 - eta) < 0 := Real.logb_neg (by norm_num) hA (by linarith)
      have hl2 : Real.logb 2 eta < 0 := Real.logb_neg (by norm_num) he (by linarith)
      simp only [g, h0, zero_mul, sub_zero, T0]
      rw [Real.logb_div he.ne' hA.ne']
      exact max_lt (by linarith) (by linarith)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
      (hg.continuousAt.eventually (lt_mem_nhds hT))
    refine ⟨δ, hδ, fun N hN hNδ hp => ?_⟩
    have := hball (y := N) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hN]; exact hNδ)
    calc twistedBound eta N ≤ T0 := s110tp_tw eta N he he1 hN hp
      _ < g N := this
      _ ≤ plobBound eta N := le_max_right _ _
  · intro N hN
    have hB : 0 < N + 1 := by linarith
    refine ⟨1 / (2 * (N + 1)), by positivity, fun eta h1 h2 h3 => ?_⟩
    have hp : 0 < eta - N * (1 - eta) := by
      rw [div_lt_iff₀ hB] at h1; linarith
    refine ⟨hp, ?_⟩
    have htw : twistedBound eta N = 0 := by
      unfold twistedBound
      apply max_eq_left
      have hA : 0 < 1 - eta := by linarith
      have hD : 0 < (1 + N) * (1 - eta) := by positivity
      apply Real.logb_nonpos (by norm_num) (div_pos hp hD).le
      rw [div_le_one hD]
      have : eta < (2 * N + 1) / (2 * (N + 1)) := by
        calc eta < N / (N + 1) + 1 / (2 * (N + 1)) := h2
          _ = (2 * N + 1) / (2 * (N + 1)) := by field_simp
      rw [lt_div_iff₀ (by positivity)] at this
      nlinarith
    rw [htw]
    exact lt_of_lt_of_le (s110tp_f eta N hN h1 h3) (le_max_right _ _)
