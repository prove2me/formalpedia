-- Prove2me | solution 1 for centered_sampling_coefficient_subgaussian_tail
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T02:05:17.162384+00:00
-- url     : https://prove2.me/submissions/e751db46-c820-4251-bf4a-db85d219a511

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_centered_sampling_chernoff_exponential_tail
import Theorems.Thm_centered_sampling_coefficient_subgaussian_mgf
import Mathlib.Analysis.SpecialFunctions.Exp

open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1000000

/-- **Sub-Gaussian tail** of the centered-sampling coefficient.
`P(t ≤ Coeff) ≤ exp(- 2 p² t² / ‖B‖_F²)` for `0 < p ≤ 1`, `0 ≤ t`, `‖B‖_F² > 0`. -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hB : 0 < frobeniusNormSq B) :
    bernoulliEventProb p
        (fun Omega =>
          t ≤ matrixEntrySum (centeredSamplingFluctuation Omega p B)) ≤
      Real.exp (-(2 * p ^ 2 * t ^ 2 / frobeniusNormSq B)) := by
  classical
  set Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Omega => matrixEntrySum (centeredSamplingFluctuation Omega p B) with hZ
  -- Optimal Chernoff parameter λ = 4 p² t / ‖B‖_F²  (≥ 0; > 0 unless t = 0).
  set lam : ℝ := 4 * p ^ 2 * t / frobeniusNormSq B with hlamdef
  -- Handle t = 0 separately (then λ = 0, Chernoff node needs λ > 0).
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · -- t = 0 : RHS = exp 0 = 1, and a probability is ≤ 1.
    rw [← ht0]
    simp only [mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_div, neg_zero, Real.exp_zero]
    -- P(0 ≤ Z) ≤ 1
    unfold bernoulliEventProb
    have hsum : ∑ Omega : Finset (Fin n₁ × Fin n₂),
        (if 0 ≤ matrixEntrySum (centeredSamplingFluctuation Omega p B)
          then bernoulliObservationWeight p Omega else 0) ≤
        ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega := by
      apply Finset.sum_le_sum
      intro Omega _
      have hw : 0 ≤ bernoulliObservationWeight p Omega := by
        unfold bernoulliObservationWeight
        have : (0:ℝ) ≤ 1 - p := by linarith
        positivity
      by_cases h : 0 ≤ matrixEntrySum (centeredSamplingFluctuation Omega p B)
      · simp [h]
      · simp [h, hw]
    refine hsum.trans ?_
    -- ∑ bernoulliObservationWeight = 1
    have hone : ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
      have hpa := Fintype.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1 - p))
      simp only [add_sub_cancel, Finset.prod_const_one] at hpa
      rw [hpa]
      apply Finset.sum_congr rfl
      intro s _
      rw [bernoulliObservationWeight, Finset.prod_const, Finset.prod_const,
        Finset.card_compl]
    rw [hone]
  · -- t > 0 : optimize the Chernoff bound.
    have hlampos : 0 < lam := by
      rw [hlamdef]; positivity
    -- Chernoff tail node with Z and lam.
    have hCher := centered_sampling_chernoff_exponential_tail (n₁ := n₁) (n₂ := n₂)
      p (le_of_lt hp0) hp1 Z t lam hlampos
    -- Sub-Gaussian MGF node.
    have hMGF := centered_sampling_coefficient_subgaussian_mgf (n₁ := n₁) (n₂ := n₂)
      p hp0 hp1 B lam
    -- E[exp(λ Z)] ≤ exp(λ² ‖B‖_F²/(8p²)); chain with Chernoff.
    have hexp_nonneg : 0 ≤ Real.exp (-(lam * t)) := (Real.exp_pos _).le
    refine hCher.trans ?_
    refine (mul_le_mul_of_nonneg_left hMGF hexp_nonneg).trans ?_
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    -- -(λ t) + λ² ‖B‖_F²/(8 p²) = - 2 p² t² / ‖B‖_F²  with λ = 4 p² t / ‖B‖_F².
    rw [hlamdef]
    have hBne : frobeniusNormSq B ≠ 0 := ne_of_gt hB
    rw [show -(4 * p ^ 2 * t / frobeniusNormSq B * t)
          + (4 * p ^ 2 * t / frobeniusNormSq B) ^ 2 * frobeniusNormSq B / (8 * p ^ 2)
        = -(2 * p ^ 2 * t ^ 2 / frobeniusNormSq B) by
      field_simp; ring]
