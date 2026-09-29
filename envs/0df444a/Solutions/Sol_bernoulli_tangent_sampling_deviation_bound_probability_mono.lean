-- Prove2me | solution 1 for bernoulli_tangent_sampling_deviation_bound_probability_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T00:35:21.967871+00:00
-- url     : https://prove2.me/submissions/a5062eb9-5ac5-49a5-9435-598305999253

import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_tangent_sampling_deviation_bound_mono
import Definitions.Def_matrix_completion_bernoulli
import Definitions.Def_matrix_completion_tangent

open MatrixCompletion


open MatrixCompletion

/-- Lift deterministic monotonicity of tangent deviation thresholds to
Bernoulli event-probability monotonicity. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p small large c β : ℝ) :
    0 ≤ p → p ≤ 1 →
    small ≤ large →
    bernoulliEventProb p
        (fun Omega => TangentSamplingDeviationBound Omega S p small) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => TangentSamplingDeviationBound Omega S p large) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hpNonneg hpLeOne hSmallLarge hProb
  have hMono :
      bernoulliEventProb p
          (fun Omega => TangentSamplingDeviationBound Omega S p small) ≤
        bernoulliEventProb p
          (fun Omega => TangentSamplingDeviationBound Omega S p large) :=
    bernoulli_event_probability_mono p
      (fun Omega => TangentSamplingDeviationBound Omega S p small)
      (fun Omega => TangentSamplingDeviationBound Omega S p large)
      hpNonneg hpLeOne
      (by
        intro Omega hBound
        exact tangent_sampling_deviation_bound_mono
          Omega S p small large hSmallLarge hBound)
  exact le_trans hProb hMono
