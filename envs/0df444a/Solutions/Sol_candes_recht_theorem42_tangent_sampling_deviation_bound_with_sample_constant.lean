-- Prove2me | solution 1 for candes_recht_theorem42_tangent_sampling_deviation_bound_with_sample_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T03:55:13.505187+00:00
-- url     : https://prove2.me/submissions/ad8d7daf-e324-4781-941f-85f8543926ef

import Theorems.Thm_candes_recht_theorem42_rudelson_expectation_bound_with_sample_constant
import Theorems.Thm_candes_recht_theorem42_talagrand_deviation_around_mean_with_sample_constant
import Theorems.Thm_sum_tangent_sampling_deviation_scales_le_single_scale
import Theorems.Thm_bernoulli_tangent_sampling_deviation_bound_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candes--Recht, PDF pp. 18--20, Theorem 4.2, equations (4.9)--(4.10),
and the paragraph immediately following equation (4.10).

The proof of the deviation bound has two analytic inputs.  First, Rudelson's
selection estimate gives `E Z` at the expectation scale and, after the sample
constant is chosen large enough, also gives `E Z ≤ 1`.  Second, the Talagrand
estimate applies under that `E Z ≤ 1` hypothesis and controls `Z` around its
mean.  This sketch only combines those two events, absorbs the two displayed
scales into one universal scale, and applies Bernoulli event monotonicity.
-/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → A0 S μ₀ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases candes_recht_theorem42_rudelson_expectation_bound_with_sample_constant with
    ⟨Cexpect, hCexpect, hExpectation⟩
  rcases candes_recht_theorem42_talagrand_deviation_around_mean_with_sample_constant with
    ⟨Ctail, ctail, hCtail, hctail, hTalagrand⟩
  rcases sum_tangent_sampling_deviation_scales_le_single_scale Cexpect Ctail
      hCexpect hCtail with
    ⟨Csum, hCsum, hSum⟩
  let C : ℝ := max (max Cexpect Ctail) Csum
  have hC_pos : 0 < C :=
    lt_of_lt_of_le hCexpect (le_trans (le_max_left Cexpect Ctail) (le_max_left _ Csum))
  refine ⟨C, ctail, hC_pos, hctail, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ S hn₁ hn₂ hr hm hμ₀ hA0 hmLower
  let n : ℕ := max n₁ n₂
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let EZ : ℝ :=
    bernoulliExpectation p
      (fun Omega => tangentSamplingDeviation Omega S p)
  have hCexpect_le_C' : Cexpect ≤ C' := by
    exact le_trans (le_trans (le_max_left Cexpect Ctail) (le_max_left _ Csum)) hC'
  have hCtail_le_C' : Ctail ≤ C' := by
    exact le_trans (le_trans (le_max_right Cexpect Ctail) (le_max_left _ Csum)) hC'
  have hCsum_le_C : Csum ≤ C := by
    exact le_max_right (max Cexpect Ctail) Csum
  rcases hExpectation C' hCexpect_le_C' β hβ n₁ n₂ r m M μ₀ S
      hn₁ hn₂ hr hm hμ₀ hA0 hmLower with
    ⟨hExpectationScale, hExpectationSmall⟩
  have hTalagrandProb :
      bernoulliEventProb p
          (fun Omega =>
            TangentSamplingDeviationBound Omega S p
              (EZ + tangentSamplingDeviationScale Ctail β μ₀ n r m)) ≥
        1 - ctail * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa [p, n, EZ] using
      hTalagrand C' hCtail_le_C' β hβ n₁ n₂ r m M μ₀ S
        hn₁ hn₂ hr hm hμ₀ hA0 hmLower hExpectationSmall
  have hSumScale :
      tangentSamplingDeviationScale Cexpect β μ₀ n r m +
          tangentSamplingDeviationScale Ctail β μ₀ n r m ≤
        tangentSamplingDeviationScale Csum β μ₀ n r m :=
    hSum β μ₀ n r m
  have hScaleMono :
      tangentSamplingDeviationScale Csum β μ₀ n r m ≤
        tangentSamplingDeviationScale C β μ₀ n r m := by
    dsimp [tangentSamplingDeviationScale]
    exact mul_le_mul_of_nonneg_right hCsum_le_C (Real.sqrt_nonneg _)
  have hThreshold :
      EZ + tangentSamplingDeviationScale Ctail β μ₀ n r m ≤
        tangentSamplingDeviationScale C β μ₀ n r m := by
    have hExp :
        EZ ≤ tangentSamplingDeviationScale Cexpect β μ₀ n r m := by
      simpa [p, n, EZ] using hExpectationScale
    calc
      EZ + tangentSamplingDeviationScale Ctail β μ₀ n r m
          ≤ tangentSamplingDeviationScale Cexpect β μ₀ n r m +
              tangentSamplingDeviationScale Ctail β μ₀ n r m := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hExp
                (tangentSamplingDeviationScale Ctail β μ₀ n r m)
      _ ≤ tangentSamplingDeviationScale Csum β μ₀ n r m := hSumScale
      _ ≤ tangentSamplingDeviationScale C β μ₀ n r m := hScaleMono
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  exact bernoulli_tangent_sampling_deviation_bound_probability_mono S p
    (EZ + tangentSamplingDeviationScale Ctail β μ₀ n r m)
    (tangentSamplingDeviationScale C β μ₀ n r m)
    ctail β hpNonneg hpLeOne hThreshold hTalagrandProb
