-- Prove2me | solution 1 for bernoulli_least_squares_certificate_normal_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T23:41:40.045712+00:00
-- url     : https://prove2.me/submissions/6e0388f9-c085-4331-b3a2-62ffaa675346

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_least_squares_certificate_normal_bound_from_neumann_term_bounds_pos
import Theorems.Thm_bernoulli_tangent_sampling_concentration_under_general_sample_bound
import Theorems.Thm_linear_neumann_correction_small_under_general_sample_bound
import Theorems.Thm_sampled_sign_matrix_neumann_term_small_under_general_sample_bound
import Theorems.Thm_quadratic_neumann_correction_small_under_general_sample_bound
import Theorems.Thm_neumann_certificate_remainder_small_under_general_sample_bound
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Sound re-decomposition of `bernoulli_least_squares_certificate_normal_bound_under_general_sample_bound`
(b4e12b11): the existing reduction routes through the disproved pointwise node 22bf6cfe
(via 8feb62b1). Here we re-derive b4e12b11 through the CORRECTED lane:

  - the corrected Bernoulli normal-bound node
    `least_squares_certificate_normal_bound_from_neumann_term_bounds_pos` (8feb62b1_pos),
    which consumes a high-probability concentration event plus the four Neumann-term
    high-probability events and outputs the normal-bound event,
  - the concentration event supplied by
    `bernoulli_tangent_sampling_concentration_under_general_sample_bound` (3dcc0a7e),
  - the four Neumann-term `_under_general_sample_bound` wrappers (sign/linear/quadratic/remainder),
  - `sample_ratio_between_zero_and_one` for `0 ≤ p ≤ 1`.

We take a uniform failure constant `c = max` of the five children's constants, weaken each
event to that constant, derive `0 < p` from the density bound (`n ≥ 2` case; the corner
`n = 1` case is closed by nonnegativity of the probability), and apply 8feb62b1_pos.

Source: Candès–Recht 2009 (arXiv:0805.4471), §4.3 (Neumann-series certificate, finite
union bound) + §4.2 (concentration/invertibility input, pp.19–20).
-/

open MatrixCompletion
open scoped Classical BigOperators

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
            (fun Omega =>
              ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
                LeastSquaresDualCertificate Omega S Y →
                spectralNorm (normalProjection S Y) < 1) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨C0, c0, hC0, hc0, hConc⟩ :=
    bernoulli_tangent_sampling_concentration_under_general_sample_bound
  obtain ⟨C1, c1, hC1, hc1, hSign⟩ :=
    sampled_sign_matrix_neumann_term_small_under_general_sample_bound
  obtain ⟨C2, c2, hC2, hc2, hLin⟩ :=
    linear_neumann_correction_small_under_general_sample_bound
  obtain ⟨C3, c3, hC3, hc3, hQuad⟩ :=
    quadratic_neumann_correction_small_under_general_sample_bound
  obtain ⟨C4, c4, hC4, hc4, hRem⟩ :=
    neumann_certificate_remainder_small_under_general_sample_bound
  set Cmax := max (max (max C0 C1) (max C2 C3)) C4 with hCmax
  set cmax := max (max (max c0 c1) (max c2 c3)) c4 with hcmax
  have hC0le : C0 ≤ Cmax := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hC1le : C1 ≤ Cmax := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hC2le : C2 ≤ Cmax := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hC3le : C3 ≤ Cmax := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hC4le : C4 ≤ Cmax := le_max_right _ _
  have hc0le : c0 ≤ cmax := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hc1le : c1 ≤ cmax := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hc2le : c2 ≤ cmax := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hc3le : c3 ≤ cmax := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hc4le : c4 ≤ cmax := le_max_right _ _
  have hCmax_pos : 0 < Cmax := lt_of_lt_of_le hC0 hC0le
  have hcmax_pos : 0 < cmax := lt_of_lt_of_le hc0 hc0le
  refine ⟨Cmax, max (5 * cmax) 1, hCmax_pos,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hGen
  have hC'0 : C0 ≤ C' := le_trans hC0le hC'
  have hC'1 : C1 ≤ C' := le_trans hC1le hC'
  have hC'2 : C2 ≤ C' := le_trans hC2le hC'
  have hC'3 : C3 ≤ C' := le_trans hC3le hC'
  have hC'4 : C4 ≤ C' := le_trans hC4le hC'
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hmax_pos : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left _ _)
  have hrpow_nn : 0 ≤ Real.rpow (↑(max n₁ n₂)) (-β) :=
    Real.rpow_nonneg (by exact_mod_cast Nat.zero_le _) _
  have hprob_nn :
      0 ≤ bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
                LeastSquaresDualCertificate Omega S Y →
                spectralNorm (normalProjection S Y) < 1) := by
    unfold bernoulliEventProb
    apply Finset.sum_nonneg
    intro Omega _
    by_cases hev : (∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
        LeastSquaresDualCertificate Omega S Y →
        spectralNorm (normalProjection S Y) < 1)
    · rw [if_pos hev]
      unfold bernoulliObservationWeight
      exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
    · rw [if_neg hev]
  by_cases hn1 : max n₁ n₂ = 1
  · -- corner n = 1: n^{-β} = 1, 1 - 5cmax·1 ≤ 0 ≤ prob.
    have hrpow1 : Real.rpow (↑(max n₁ n₂)) (-β) = 1 := by rw [hn1]; simp
    rw [ge_iff_le, hrpow1, mul_one]
    have hge1 : (1 : ℝ) ≤ max (5 * cmax) 1 := le_max_right _ _
    linarith [hprob_nn, hge1]
  · -- main n ≥ 2: derive 0 < p, gather the 5 events at uniform cmax, apply 8feb62b1_pos.
    have hmax_ge2 : 2 ≤ max n₁ n₂ := by omega
    have hmaxR2 : (2 : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by exact_mod_cast hmax_ge2
    have hlog_pos : 0 < Real.log (↑(max n₁ n₂)) := Real.log_pos (by linarith)
    have hβ_pos : (0 : ℝ) < β := lt_trans (by norm_num) hβ
    have hrp_ge1 : (1 : ℝ) ≤ Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    have hinner_pos :
        0 < max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) := by
      have h1 : (1 : ℝ) ≤ μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4) := by
        nlinarith [hrp_ge1, hμ₀]
      have h2 := le_max_right (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
      linarith [le_trans h1 h2]
    have hC'_pos : 0 < C' := lt_of_lt_of_le hC0 hC'0
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
    -- the 5 events at their own constants, then weaken to cmax
    have eConc := hConc C' hC'0 β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hGen
    have eSign := hSign C' hC'1 β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hGen
    have eLin := hLin C' hC'2 β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hGen
    have eQuad := hQuad C' hC'3 β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hGen
    have eRem := hRem C' hC'4 β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hGen
    -- weakening helper: 1 - cmax·fs ≤ 1 - cᵢ·fs and chain through eᵢ
    have wk : ∀ (ci : ℝ), ci ≤ cmax →
        ∀ (P : Real),
          P ≥ 1 - ci * Real.rpow (↑(max n₁ n₂)) (-β) →
          P ≥ 1 - cmax * Real.rpow (↑(max n₁ n₂)) (-β) := by
      intro ci hcile P hP
      have := mul_le_mul_of_nonneg_right hcile hrpow_nn
      linarith
    have eConc' := wk c0 hc0le _ eConc
    have eSign' := wk c1 hc1le _ eSign
    have eLin' := wk c2 hc2le _ eLin
    have eQuad' := wk c3 hc3le _ eQuad
    have eRem' := wk c4 hc4le _ eRem
    -- apply the corrected normal-bound node 8feb62b1_pos (output 1 - 5·cmax·fs)
    have hmain := least_squares_certificate_normal_bound_from_neumann_term_bounds_pos
      S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) cmax β hp_pos hp1
      eConc' eSign' eLin' eQuad' eRem'
    -- weaken 5·cmax to max (5·cmax) 1
    have hfinal : 1 - max (5 * cmax) 1 * Real.rpow (↑(max n₁ n₂)) (-β)
        ≤ 1 - (5 * cmax) * Real.rpow (↑(max n₁ n₂)) (-β) := by
      have := mul_le_mul_of_nonneg_right (le_max_left (5 * cmax) 1) hrpow_nn
      linarith
    exact le_trans hfinal hmain
