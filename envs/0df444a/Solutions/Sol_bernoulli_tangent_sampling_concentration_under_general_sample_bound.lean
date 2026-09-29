-- Prove2me | solution 1 for bernoulli_tangent_sampling_concentration_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T02:40:39.089547+00:00
-- url     : https://prove2.me/submissions/7e664e86-b4f3-416e-a1e7-ecb8279f69ef

import Theorems.Thm_candes_recht_theorem41_bernoulli_tangent_sampling_concentration
import Mathlib.Tactic

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF pp. 18--20, Theorem 4.1 and equations
(4.5), (4.9), (4.10).

This sketch is only the sample-regime bridge.  The child theorem is the
paper-level Bernoulli tangent concentration result with its universal sample
constant.  The general Theorem 1.3 lower bound implies the child lower bound
because the incoherence factor
`max (max μ₁^2 (sqrt μ₀ * μ₁)) (μ₀ * n^(1/4))` is at least `μ₀` for `n ≥ 1`,
and the outer universal constant is chosen large enough. -/
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
              TangentSamplingConcentration Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ((1 : ℝ) / 2)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases candes_recht_theorem41_bernoulli_tangent_sampling_concentration with
    ⟨C41, c41, hC41, hc41, hTheorem41⟩
  let C : ℝ := max C41 1
  have hC_pos : 0 < C := lt_of_lt_of_le hC41 (le_max_left C41 1)
  refine ⟨C, c41, hC_pos, hc41, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  let n : ℕ := max n₁ n₂
  let K : ℝ :=
    max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
      (μ₀ * Real.rpow (n : ℝ) ((1 : ℝ) / 4))
  have hC41_le_C' : C41 ≤ C' := le_trans (le_max_left C41 1) hC'
  have hOne_le_C' : (1 : ℝ) ≤ C' := le_trans (le_max_right C41 1) hC'
  have hC'_nonneg : 0 ≤ C' := le_trans zero_le_one hOne_le_C'
  have hn : 0 < n := by
    dsimp [n]
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hn_real_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hn_rpow_ge_one :
      (1 : ℝ) ≤ Real.rpow (n : ℝ) ((1 : ℝ) / 4) := by
    exact Real.one_le_rpow hn_real_ge_one (by norm_num)
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hμ₀_le_term :
      μ₀ ≤ μ₀ * Real.rpow (n : ℝ) ((1 : ℝ) / 4) := by
    nlinarith [mul_le_mul_of_nonneg_left hn_rpow_ge_one hμ₀_nonneg]
  have hterm_le_K :
      μ₀ * Real.rpow (n : ℝ) ((1 : ℝ) / 4) ≤ K := by
    dsimp [K]
    exact le_max_right _ _
  have hμ₀_le_K : μ₀ ≤ K := le_trans hμ₀_le_term hterm_le_K
  have hC41_nonneg : 0 ≤ C41 := le_of_lt hC41
  have hC41μ₀_le_C'K : C41 * μ₀ ≤ C' * K := by
    exact mul_le_mul hC41_le_C' hμ₀_le_K hμ₀_nonneg hC'_nonneg
  have hβ_nonneg : 0 ≤ β := le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 2) hβ)
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_real_ge_one
  have htail_nonneg :
      0 ≤ (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ)) := by
    positivity
  have hTheorem41Lower :
      (m : ℝ) ≥ C41 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
        (β * Real.log (↑(max n₁ n₂))) := by
    have hle :
        (C41 * μ₀) * ((n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ))) ≤
          (C' * K) * ((n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hC41μ₀_le_C'K htail_nonneg
    calc
      C41 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          (β * Real.log (↑(max n₁ n₂)))
          = (C41 * μ₀) * ((n : ℝ) * (r : ℝ) *
              (β * Real.log (n : ℝ))) := by
            simp [n]
            ring
      _ ≤ (C' * K) * ((n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ))) := hle
      _ = C' * K * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ)) := by ring
      _ ≤ (m : ℝ) := by
        simpa [n, K, C, mul_assoc] using hmLower
  exact hTheorem41 C41 (le_refl C41) β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hTheorem41Lower
