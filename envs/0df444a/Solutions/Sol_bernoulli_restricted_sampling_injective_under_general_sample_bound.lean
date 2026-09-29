-- Prove2me | solution 1 for bernoulli_restricted_sampling_injective_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T18:25:34.007461+00:00
-- url     : https://prove2.me/submissions/7ad2b161-fd9c-4033-869f-841e1d8b3d3e

import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_bernoulli_tangent_sampling_concentration_under_general_sample_bound
import Theorems.Thm_bernoulli_restricted_sampling_injectivity_from_tangent_concentration_pos
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators

/-! SOUND REWIRE of `bernoulli_restricted_sampling_injective_under_general_sample_bound`
    (f9de16d0).

    The previous reduction imported the DISPROVED converter
    `bernoulli_restricted_sampling_injectivity_from_tangent_concentration` (03fa1250),
    which omitted the `0 < p` hypothesis and is false at `p = 0` (Ω = ∅: concentration
    holds vacuously but P_Ω is not injective on a nontrivial T).

    This reduction replaces it with the corrected `_pos` converter (62bfabbd) and supplies
    `0 < p` honestly from the general sample bound, plus the concentration tail from the
    reconnection node 3dcc0a7e.

    Children:
    - `bernoulli_tangent_sampling_concentration_under_general_sample_bound` (3dcc0a7e):
      high-prob tangent concentration at scale 1/2 under the general sample bound.
    - `bernoulli_restricted_sampling_injectivity_from_tangent_concentration_pos` (62bfabbd,
      my corrected converter): concentration tail + `0<p` ⟹ injectivity tail.
    - `sample_ratio_between_zero_and_one` (c0188309, Proved): `0 ≤ p ≤ 1`.

    Corner handling: when `n = max(n₁,n₂) = 1` the density RHS vanishes (`log 1 = 0`) and
    we cannot force `p > 0`; but then `n^{-β} = 1`, so taking the failure constant `c ≥ 1`
    makes `1 - c·n^{-β} = 1 - c ≤ 0 ≤ bernoulliEventProb` (probabilities are nonnegative),
    and the claim holds trivially.  For `n ≥ 2` the density RHS is strictly positive, so
    `m ≥ 1` and `p = m/(n₁n₂) > 0`, and the `_pos` converter applies.

    Source: Candès–Recht 2009, arXiv:0805.4471, §4.2 "The injectivity property",
    Theorem 4.1 eq. (4.5)/(4.11), pp. 19–20. -/

theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega => SamplingOperatorInjectiveOnT Omega S) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨C_conc, c_conc, hC_conc, hc_conc, hConc⟩ :=
    bernoulli_tangent_sampling_concentration_under_general_sample_bound
  refine ⟨max C_conc 1, max c_conc 1,
    lt_of_lt_of_le hC_conc (le_max_left _ _),
    lt_of_lt_of_le hc_conc (le_max_left _ _), ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hGen
  have hC'_conc : C_conc ≤ C' := le_trans (le_max_left _ _) hC'
  have hc_le : c_conc ≤ max c_conc 1 := le_max_left _ _
  have hc1 : (1 : ℝ) ≤ max c_conc 1 := le_max_right _ _
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  -- rpow term is nonnegative
  have hmax_pos : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left _ _)
  have hmaxR : (1 : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by exact_mod_cast hmax_pos
  have hrpow_nn : 0 ≤ Real.rpow (↑(max n₁ n₂)) (-β) :=
    Real.rpow_nonneg (by linarith) _
  -- bernoulliEventProb of the injectivity event is ≥ 0 (sum of nonneg weights).
  have hprob_nn :
      0 ≤ bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega => SamplingOperatorInjectiveOnT Omega S) := by
    unfold bernoulliEventProb
    apply Finset.sum_nonneg
    intro Omega _
    by_cases hev : SamplingOperatorInjectiveOnT Omega S
    · rw [if_pos hev]
      unfold bernoulliObservationWeight
      exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
    · rw [if_neg hev]
  -- Case split on whether n = 1.
  by_cases hn1 : max n₁ n₂ = 1
  · -- corner: n^{-β} = 1, so 1 - c·1 = 1 - c ≤ 0 ≤ prob
    have hrpow1 : Real.rpow (↑(max n₁ n₂)) (-β) = 1 := by
      rw [hn1]; simp
    rw [ge_iff_le, hrpow1, mul_one]
    have : (1 : ℝ) - max c_conc 1 ≤ 0 := by linarith
    linarith [hprob_nn, this]
  · -- main: n ≥ 2, so density RHS > 0, hence m ≥ 1 and p > 0.
    have hmax_ge2 : 2 ≤ max n₁ n₂ := by omega
    have hmaxR2 : (2 : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by exact_mod_cast hmax_ge2
    have hlog_pos : 0 < Real.log (↑(max n₁ n₂)) :=
      Real.log_pos (by linarith)
    have hβ_pos : (0 : ℝ) < β := lt_trans (by norm_num) hβ
    -- inner max ≥ μ₀ · n^{1/4} ≥ 1 · 1 = 1 > 0
    have hrp_ge1 : (1 : ℝ) ≤ Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4) :=
      Real.one_le_rpow hmaxR (by norm_num)
    have hinner_pos :
        0 < max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) := by
      have h1 : (1 : ℝ) ≤ μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4) := by
        nlinarith [hrp_ge1, hμ₀]
      have h2 := le_max_right (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
      linarith [le_trans h1 h2]
    have hC'_pos : 0 < C' := lt_of_lt_of_le hC_conc hC'_conc
    -- density RHS > 0
    have hrhs_pos :
        0 < C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) := by
      have hnR : (0 : ℝ) < (↑(max n₁ n₂) : ℝ) := by linarith
      have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
      have hblog : 0 < β * Real.log (↑(max n₁ n₂)) := mul_pos hβ_pos hlog_pos
      positivity
    have hmR_pos : 0 < (m : ℝ) := lt_of_lt_of_le hrhs_pos hGen
    have hp_pos : 0 < ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
      have hn1R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
      have hn2R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
      exact div_pos hmR_pos (mul_pos hn1R hn2R)
    -- concentration tail from 3dcc0a7e
    have hConcTail :=
      hConc C' hC'_conc β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hGen
    -- apply the corrected _pos converter
    have hInjTail :=
      bernoulli_restricted_sampling_injectivity_from_tangent_concentration_pos
        S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) c_conc β hp_pos hp1 hConcTail
    -- weaken c_conc to max c_conc 1
    have hweaken :
        1 - max c_conc 1 * Real.rpow (↑(max n₁ n₂)) (-β)
          ≤ 1 - c_conc * Real.rpow (↑(max n₁ n₂)) (-β) := by
      have := mul_le_mul_of_nonneg_right hc_le hrpow_nn
      linarith
    exact le_trans hweaken hInjTail
