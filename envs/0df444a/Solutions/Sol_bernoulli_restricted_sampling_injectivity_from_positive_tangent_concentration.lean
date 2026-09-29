-- Prove2me | solution 1 for bernoulli_restricted_sampling_injectivity_from_positive_tangent_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T06:02:43.437216+00:00
-- url     : https://prove2.me/submissions/e2116492-3b26-4290-a829-36a85ca5976b

import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_positive_tangent_sampling_concentration_implies_restricted_sampling_injective

open MatrixCompletion

/-- Lift the positive-rate deterministic injectivity implication through
Bernoulli event monotonicity. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p c β : ℝ) :
    0 < p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p (fun Omega => SamplingOperatorInjectiveOnT Omega S) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hp hp_one hconc
  have hp_nonneg : 0 ≤ p := le_of_lt hp
  have hmono :
      bernoulliEventProb p
          (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) ≤
        bernoulliEventProb p
          (fun Omega => SamplingOperatorInjectiveOnT Omega S) :=
    bernoulli_event_probability_mono p
      (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2))
      (fun Omega => SamplingOperatorInjectiveOnT Omega S)
      hp_nonneg hp_one
      (fun Omega hOmega =>
        positive_tangent_sampling_concentration_implies_restricted_sampling_injective
          Omega S p hp hOmega)
  exact le_trans hconc hmono
