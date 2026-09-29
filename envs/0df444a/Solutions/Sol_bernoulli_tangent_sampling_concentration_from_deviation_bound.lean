-- Prove2me | solution 1 for bernoulli_tangent_sampling_concentration_from_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T12:58:18.437563+00:00
-- url     : https://prove2.me/submissions/7a127114-ccb4-478b-b48e-d79fd138b4f4

import Theorems.Thm_bernoulli_tangent_sampling_concentration_from_positive_deviation_bound
import Theorems.Thm_bernoulli_tangent_sampling_concentration_from_zero_rate_deviation_bound

open MatrixCompletion

/-- Repaired proof of the Bernoulli deviation-to-concentration transfer.  The
old reduction incorrectly used a deterministic implication at `p = 0`; this
version splits off the zero-rate case. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p epsilon c β : ℝ) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingDeviationBound Omega S p epsilon) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p epsilon) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hp hp_one hdev
  by_cases hpzero : p = 0
  · subst p
    exact bernoulli_tangent_sampling_concentration_from_zero_rate_deviation_bound
      S epsilon c β hdev
  · have hpos : 0 < p := lt_of_le_of_ne hp (Ne.symm hpzero)
    exact bernoulli_tangent_sampling_concentration_from_positive_deviation_bound
      S p epsilon c β hpos hp_one hdev
