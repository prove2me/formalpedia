-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.dilation_det
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:33:55.405006+00:00
-- url     : https://prove2.me/submissions/7032243c-a7a9-4b8d-97bb-c5c47d679047

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

open ShorNonsmooth.SpaceDilation in
theorem dilation_toMatrix_754acd34 {n : ℕ} (α : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (dilation α ξ).toLinearMap =
      1 + Matrix.replicateCol Unit (fun i => ξ i) *
        Matrix.replicateRow Unit (fun j => (α - 1) * ξ j) := by
  ext i j
  simp [LinearMap.toMatrix_apply, dilation, Matrix.one_apply, Matrix.mul_apply,
    EuclideanSpace.inner_single_right, Pi.single_apply]
  split_ifs <;> ring

open ShorNonsmooth.SpaceDilation in
theorem solution {n : ℕ} (hn : 0 < n) (α : ℝ) (ξ : EuclideanSpace ℝ (Fin n))
    (hξ : ‖ξ‖ = 1) :
    LinearMap.det (dilation α ξ).toLinearMap = α := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
    dilation_toMatrix_754acd34, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have h2 : ∑ i, ξ i * ξ i = 1 := by
    have := EuclideanSpace.norm_eq ξ
    rw [hξ] at this
    have h3 : (1:ℝ) = (∑ i, ‖ξ i‖ ^ 2) := by
      have := congrArg (· ^ 2) this
      simp only [one_pow] at this
      rw [this, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    rw [h3]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, sq]
  simp only [dotProduct]
  have : ∑ i, (α - 1) * ξ i * ξ i = (α - 1) * ∑ i, ξ i * ξ i := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)
  rw [this, h2]; ring
