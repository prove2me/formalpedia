-- Prove2me | solution 1 for bernoulli_tangent_sampling_concentration_from_positive_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T06:27:00.303445+00:00
-- url     : https://prove2.me/submissions/38b0d785-bceb-4d08-a764-e650d2dae636

import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_positive_tangent_sampling_deviation_bound_implies_concentration

open MatrixCompletion

/-- Lift the positive-rate deterministic deviation-to-concentration implication
through Bernoulli event monotonicity. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p epsilon c β : ℝ) :
    0 < p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingDeviationBound Omega S p epsilon) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p epsilon) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hp hp_one hdev
  have hmono :
      bernoulliEventProb p
          (fun Omega => TangentSamplingDeviationBound Omega S p epsilon) ≤
        bernoulliEventProb p
          (fun Omega => TangentSamplingConcentration Omega S p epsilon) :=
    bernoulli_event_probability_mono p
      (fun Omega => TangentSamplingDeviationBound Omega S p epsilon)
      (fun Omega => TangentSamplingConcentration Omega S p epsilon)
      (le_of_lt hp) hp_one
      (fun Omega hOmega =>
        positive_tangent_sampling_deviation_bound_implies_concentration
          Omega S p epsilon hp hOmega)
  exact le_trans hdev hmono
