-- Prove2me | solution 1 for bernoulli_strict_dual_certificate_from_least_squares_certificate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-13T23:40:50.825144+00:00
-- url     : https://prove2.me/submissions/2dc4c1ab-491a-4c55-8aa6-e84652436214

import Theorems.Thm_bernoulli_event_intersection_probability_from_lower_bounds
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_least_squares_certificate_with_normal_bound_is_strict_dual_certificate
import Definitions.Def_matrix_completion_tangent

open MatrixCompletion


open MatrixCompletion

/-- Intersect the existence and normal-bound events, then map their intersection
to the strict-certificate event. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p cExists cNormal β : ℝ) :
    0 ≤ p → p ≤ 1 →
    0 < cExists → 0 < cNormal →
    bernoulliEventProb p
        (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
          LeastSquaresDualCertificate Omega S Y) ≥
        1 - cExists * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega =>
          ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
            LeastSquaresDualCertificate Omega S Y →
            spectralNorm (normalProjection S Y) < 1) ≥
        1 - cNormal * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
          StrictDualCertificate Omega S Y) ≥
        1 - (cExists + cNormal) *
          Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hpNonneg hpLeOne hcExists hcNormal hExistsProb hNormalProb
  have hIntersectionProb :=
    bernoulli_event_intersection_probability_from_lower_bounds
      p cExists cNormal (Real.rpow (↑(max n₁ n₂)) (-β))
      (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
        LeastSquaresDualCertificate Omega S Y)
      (fun Omega =>
        ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
          LeastSquaresDualCertificate Omega S Y →
          spectralNorm (normalProjection S Y) < 1)
      hpNonneg hpLeOne hExistsProb hNormalProb
  have hEventMono :
      bernoulliEventProb p
          (fun Omega =>
            (∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
              LeastSquaresDualCertificate Omega S Y) ∧
              ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
                LeastSquaresDualCertificate Omega S Y →
                spectralNorm (normalProjection S Y) < 1) ≤
        bernoulliEventProb p
          (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
            StrictDualCertificate Omega S Y) :=
    bernoulli_event_probability_mono p
      (fun Omega =>
        (∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
          LeastSquaresDualCertificate Omega S Y) ∧
          ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
            LeastSquaresDualCertificate Omega S Y →
            spectralNorm (normalProjection S Y) < 1)
      (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
        StrictDualCertificate Omega S Y)
      hpNonneg hpLeOne
      (by
        intro Omega hGood
        rcases hGood.1 with ⟨Y, hLeastSquares⟩
        exact ⟨Y,
          least_squares_certificate_with_normal_bound_is_strict_dual_certificate
            S Omega Y hLeastSquares (hGood.2 Y hLeastSquares)⟩)
  exact le_trans hIntersectionProb hEventMono
