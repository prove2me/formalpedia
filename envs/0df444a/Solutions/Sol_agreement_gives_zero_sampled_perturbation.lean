-- Prove2me | solution 1 for agreement_gives_zero_sampled_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-15T15:18:48.471637+00:00
-- url     : https://prove2.me/submissions/44be243e-f9ea-474b-9fda-4f32bde8bc6b

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion


open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂))
    (X M : Matrix (Fin n₁) (Fin n₂) ℝ) :
    AgreesOn Omega X M →
    samplingProjection Omega (X - M) = 0 := by
  intro hagree
  ext i j
  by_cases hmem : (i, j) ∈ Omega
  · have hXM : X i j = M i j := hagree (i, j) hmem
    simp [samplingProjection, hmem, hXM]
  · simp [samplingProjection, hmem]
