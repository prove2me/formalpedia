-- Prove2me | solution 1 for RobustRegLasso.FeatureWise.eq_4_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:21:13.137999+00:00
-- url     : https://prove2.me/submissions/cfacd989-8979-4d0f-a392-4a81a8e4c1ed

import Mathlib
import Definitions.Def_RobustRegLasso_FeatureWise_Basic

open RobustRegLasso.FeatureWise

theorem solution {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (x : Fin m → ℝ)
    (δ : Fin m → EuclideanSpace ℝ (Fin n)) (hδ : δ ∈ uncertaintySet c) :
    perturbedResidual a δ b x ≤ ‖b - matVec a x‖ + ∑ i, |x i| * c i := by
  have hmat : matVec (a + δ) x = matVec a x + matVec δ x := by
    simp [matVec, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  unfold perturbedResidual
  rw [hmat, sub_add_eq_sub_sub]
  calc
    ‖b - matVec a x - matVec δ x‖ ≤ ‖b - matVec a x‖ + ‖matVec δ x‖ :=
      norm_sub_le _ _
    _ ≤ ‖b - matVec a x‖ + ∑ i, ‖x i • δ i‖ := by
      exact add_le_add (le_refl _) (norm_sum_le Finset.univ (fun i => x i • δ i))
    _ ≤ ‖b - matVec a x‖ + ∑ i, |x i| * c i := by
      apply add_le_add (le_refl _)
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hδ i) (abs_nonneg _)

#print axioms solution
