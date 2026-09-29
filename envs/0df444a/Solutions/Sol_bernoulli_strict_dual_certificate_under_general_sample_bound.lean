-- Prove2me | solution 1 for bernoulli_strict_dual_certificate_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:09:20.515779+00:00
-- url     : https://prove2.me/submissions/1a639bd0-b17c-44f5-8f3b-44d12a94946a

import Theorems.Thm_bernoulli_least_squares_certificate_exists_under_general_sample_bound
import Theorems.Thm_bernoulli_least_squares_certificate_normal_bound_under_general_sample_bound
import Theorems.Thm_bernoulli_strict_dual_certificate_from_least_squares_certificate_bounds
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Third-layer reduction of the strict dual-certificate theorem: construct the
least-squares certificate, prove its normal component is strictly small, and
combine the two high-probability events. -/
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
            (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
              StrictDualCertificate Omega S Y) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases bernoulli_least_squares_certificate_exists_under_general_sample_bound with
    ⟨CExists, cExists, hCExists, hcExists, hExists⟩
  rcases bernoulli_least_squares_certificate_normal_bound_under_general_sample_bound with
    ⟨CNormal, cNormal, hCNormal, hcNormal, hNormal⟩
  refine ⟨max CExists CNormal, cExists + cNormal,
    lt_of_lt_of_le hCExists (le_max_left _ _),
    add_pos hcExists hcNormal, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hCExists' : CExists ≤ C' := le_trans (le_max_left _ _) hC'
  have hCNormal' : CNormal ≤ C' := le_trans (le_max_right _ _) hC'
  have hExistsProb :=
    hExists C' hCExists' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hNormalProb :=
    hNormal C' hCNormal' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  exact bernoulli_strict_dual_certificate_from_least_squares_certificate_bounds S
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) cExists cNormal β
    hpNonneg hpLeOne hcExists hcNormal hExistsProb hNormalProb
