-- Prove2me | solution 1 for bernoulli_neumann_certificate_term_bound_probability_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T00:12:33.733058+00:00
-- url     : https://prove2.me/submissions/af0fba07-9810-4c80-aaf0-426f9435907c

import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_neumann_certificate_term_spectral_bound_mono
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Lift deterministic threshold monotonicity for a Neumann term to Bernoulli
event-probability monotonicity. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p : ℝ) (k : ℕ) (small large c β : ℝ) :
    0 ≤ p → p ≤ 1 →
    small ≤ large →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTermSpectralBound Omega S p k small) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => NeumannCertificateTermSpectralBound Omega S p k large) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hpNonneg hpLeOne hSmallLarge hProb
  have hMono :
      bernoulliEventProb p
          (fun Omega => NeumannCertificateTermSpectralBound Omega S p k small) ≤
        bernoulliEventProb p
          (fun Omega => NeumannCertificateTermSpectralBound Omega S p k large) :=
    bernoulli_event_probability_mono p
      (fun Omega => NeumannCertificateTermSpectralBound Omega S p k small)
      (fun Omega => NeumannCertificateTermSpectralBound Omega S p k large)
      hpNonneg hpLeOne
      (by
        intro Omega hBound
        exact neumann_certificate_term_spectral_bound_mono
          S Omega p k small large hSmallLarge hBound)
  exact le_trans hProb hMono
