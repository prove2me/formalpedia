-- Prove2me | solution 1 for bernoulli_tangent_sampling_concentration_from_zero_rate_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T06:37:20.313985+00:00
-- url     : https://prove2.me/submissions/bd56bd2c-4b33-4c10-89a8-b1da384100b0

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

open scoped Classical BigOperators

private lemma tangentProjection_zero
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) :
    tangentProjection S (0 : Matrix (Fin n₁) (Fin n₂) ℝ) = 0 := by
  ext i j
  simp [tangentProjection, leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection]

private lemma samplingProjection_empty
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    samplingProjection (∅ : Finset (Fin n₁ × Fin n₂)) X = 0 := by
  ext i j
  simp [samplingProjection]

private lemma empty_zero_rate_tangent_concentration
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (epsilon : ℝ) :
    TangentSamplingConcentration
      (∅ : Finset (Fin n₁ × Fin n₂)) S 0 epsilon := by
  intro X _hX
  rw [samplingProjection_empty X, tangentProjection_zero S]
  simp [frobeniusNorm, frobeniusNormSq]

private lemma zero_rate_nonempty_weight
    {n₁ n₂ : ℕ} {Omega : Finset (Fin n₁ × Fin n₂)}
    (hOmega : Omega ≠ ∅) :
    bernoulliObservationWeight 0 Omega = 0 := by
  have hcard : Omega.card ≠ 0 := by
    intro h
    exact hOmega (Finset.card_eq_zero.mp h)
  unfold bernoulliObservationWeight
  simp [zero_pow hcard]

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (epsilon c β : ℝ) :
    bernoulliEventProb (n1 := n₁) (n2 := n₂) 0
        (fun Omega => TangentSamplingDeviationBound Omega S 0 epsilon) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb (n1 := n₁) (n2 := n₂) 0
        (fun Omega => TangentSamplingConcentration Omega S 0 epsilon) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hdev
  refine le_trans hdev ?_
  unfold bernoulliEventProb
  apply Finset.sum_le_sum
  intro Omega _
  by_cases hEmpty : Omega = ∅
  · subst Omega
    have hConc := empty_zero_rate_tangent_concentration S epsilon
    by_cases hDev :
        TangentSamplingDeviationBound
          (∅ : Finset (Fin n₁ × Fin n₂)) S 0 epsilon
    · simp [hDev, hConc]
    · have hweight_nonneg :
          0 ≤ bernoulliObservationWeight (n1 := n₁) (n2 := n₂) 0
            (∅ : Finset (Fin n₁ × Fin n₂)) := by
        unfold bernoulliObservationWeight
        positivity
      simp [hDev, hConc, hweight_nonneg]
  · have hweight : bernoulliObservationWeight (n1 := n₁) (n2 := n₂) 0 Omega = 0 :=
      zero_rate_nonempty_weight hEmpty
    simp [hweight]
