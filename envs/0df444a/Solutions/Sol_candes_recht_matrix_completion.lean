-- Prove2me | solution 1 for candes_recht_matrix_completion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:41.478289+00:00
-- url     : https://prove2.me/submissions/96e333b5-7e9c-4fd0-8511-7563975676bc

import Theorems.Thm_bernoulli_exact_completion_general_sample_complexity
import Theorems.Thm_fixed_cardinality_completion_probability_from_bernoulli_model
import Mathlib.Tactic.NormNum

open MatrixCompletion

/-- First-layer reduction for the general branch of Candes-Recht Theorem 1.3:
prove the theorem in the Bernoulli model, then transfer the probability bound to
uniform fixed-cardinality sampling. -/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        successProb m M ≥ 1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases bernoulli_exact_completion_general_sample_complexity with
    ⟨C, c, hC, hc, hBernoulli⟩
  refine ⟨C, 2 * c, hC, mul_pos (by norm_num : (0 : ℝ) < 2) hc, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  exact fixed_cardinality_completion_probability_from_bernoulli_model
    n₁ n₂ m M c β
    hn₁ hn₂ hm hc hβ
    (hBernoulli β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower)
