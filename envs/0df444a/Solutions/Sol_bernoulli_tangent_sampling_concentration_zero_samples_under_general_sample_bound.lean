-- Prove2me | solution 1 for bernoulli_tangent_sampling_concentration_zero_samples_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-24T22:48:13.155731+00:00
-- url     : https://prove2.me/submissions/a0abd7fc-7064-4d37-be04-f4e6d77219f3

import Theorems.Thm_bernoulli_event_prob_nonneg
import Definitions.Def_matrix_completion_tangent
import Mathlib.Tactic

open MatrixCompletion

theorem solution
    (C' c β : ℝ)
    (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
    (μ₀ μ₁ : ℝ) (S : SVD M r) :
    0 < C' → 1 ≤ c → 2 < β →
    0 < n₁ → 0 < n₂ → 0 < r → m = 0 → m ≤ n₁ * n₂ →
    1 ≤ μ₀ → 1 ≤ μ₁ →
    (m : ℝ) ≥
      C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
              (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
        * (↑(max n₁ n₂)) * (r : ℝ) *
          (β * Real.log (↑(max n₁ n₂))) →
    bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (fun Omega =>
          TangentSamplingConcentration Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ((1 : ℝ) / 2)) ≥
      1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hC' hc hβ hn₁ hn₂ hr hm0 _hmle hμ₀ _hμ₁ hsample
  subst m
  let scale : ℝ := max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
      (μ₀ * Real.rpow (↑(max n₁ n₂) : ℝ) ((1 : ℝ) / 4))
  have hn_ge_one_nat : 1 ≤ max n₁ n₂ := by
    exact Nat.succ_le_iff.mp (lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂))
  have hn_eq_one : max n₁ n₂ = 1 := by
    by_cases hN : max n₁ n₂ = 1
    · exact hN
    have hN_gt_one : 1 < max n₁ n₂ := lt_of_le_of_ne hn_ge_one_nat (Ne.symm hN)
    have hN_pos_nat : 0 < max n₁ n₂ := lt_trans Nat.zero_lt_one hN_gt_one
    have hN_pos : (0 : ℝ) < (max n₁ n₂ : ℝ) := by exact_mod_cast hN_pos_nat
    have hN_gt_one_real : (1 : ℝ) < (max n₁ n₂ : ℝ) := by exact_mod_cast hN_gt_one
    have hlog_pos : 0 < Real.log (↑(max n₁ n₂) : ℝ) :=
      Real.log_pos (by simpa [Nat.cast_max] using hN_gt_one_real)
    have hμ₀_pos : 0 < μ₀ := by linarith
    have hrpow_pos :
        0 < Real.rpow (↑(max n₁ n₂) : ℝ) ((1 : ℝ) / 4) :=
      Real.rpow_pos_of_pos (by simpa [Nat.cast_max] using hN_pos) _
    have hscale_pos : 0 < scale := by
      have harg_pos :
          0 < μ₀ * Real.rpow (↑(max n₁ n₂) : ℝ) ((1 : ℝ) / 4) :=
        mul_pos hμ₀_pos hrpow_pos
      exact lt_of_lt_of_le harg_pos (by
        dsimp [scale]
        exact le_max_right _ _)
    have hsource_pos :
        0 <
          C' * scale * (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂) : ℝ)) := by
      positivity
    have hzero_ge :
        (0 : ℝ) ≥
          C' * scale * (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂) : ℝ)) := by
      simpa [scale] using hsample
    linarith
  have hp0 :
      0 ≤ ((0 : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by norm_num
  have hp1 :
      ((0 : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ≤ 1 := by norm_num
  have hprob_nonneg :
      0 ≤ bernoulliEventProb ((0 : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (fun Omega =>
          TangentSamplingConcentration Omega S
            ((0 : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ((1 : ℝ) / 2)) :=
    bernoulli_event_prob_nonneg
      (fun Omega =>
        TangentSamplingConcentration Omega S
          ((0 : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ((1 : ℝ) / 2)) hp0 hp1
  have htail_nonpos :
      1 - c * Real.rpow (↑(max n₁ n₂) : ℝ) (-β) ≤ 0 := by
    rw [hn_eq_one]
    norm_num
    linarith
  simpa using htail_nonpos.trans hprob_nonneg
