-- Prove2me | solution 1 for StatUnlearn.mahalanobis_triangle
-- status  : ACCEPTED   (prove)
-- author  : @2017Advanced@
-- created : 2026-11-06T18:44:12.749839+00:00
-- url     : https://prove2.me/submissions/0ac94b6d-4e50-4d2e-80cf-b5999edc49e8

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
open MeasureTheory
open scoped MatrixOrder

theorem solution {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (x y : EuclideanSpace ℝ (Fin d)) :
    Real.sqrt (inner ℝ (x + y) (Matrix.toEuclideanLin S⁻¹ (x + y)))
      ≤ Real.sqrt (inner ℝ x (Matrix.toEuclideanLin S⁻¹ x))
        + Real.sqrt (inner ℝ y (Matrix.toEuclideanLin S⁻¹ y)) := by
  set T : Matrix (Fin d) (Fin d) ℝ := CFC.sqrt S⁻¹ with hT
  have hSinv : (0 : Matrix (Fin d) (Fin d) ℝ) ≤ S⁻¹ := hS.inv.posSemidef.nonneg
  have hTsq : T * T = S⁻¹ := by
    have h := CFC.sq_sqrt (S⁻¹) hSinv
    rw [pow_two] at h
    simpa [hT] using h
  have hTsymm : T.IsHermitian := by
    have : T.PosSemidef := by
      rw [← Matrix.nonneg_iff_posSemidef]
      exact CFC.sqrt_nonneg S⁻¹
    exact this.isHermitian
  have hadj : (Matrix.toEuclideanLin T).adjoint = Matrix.toEuclideanLin T := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hTsymm.eq]
  -- `ρ u = ‖T u‖`
  have hkey : ∀ u : EuclideanSpace ℝ (Fin d),
      inner ℝ u (Matrix.toEuclideanLin S⁻¹ u) = ‖Matrix.toEuclideanLin T u‖ ^ 2 := by
    intro u
    have hmul : Matrix.toEuclideanLin S⁻¹ u
        = Matrix.toEuclideanLin T (Matrix.toEuclideanLin T u) := by
      rw [← hTsq, Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply,
        Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec]
    rw [hmul]
    calc inner ℝ u (Matrix.toEuclideanLin T (Matrix.toEuclideanLin T u))
        = inner ℝ ((Matrix.toEuclideanLin T).adjoint u) (Matrix.toEuclideanLin T u) :=
          (LinearMap.adjoint_inner_left (Matrix.toEuclideanLin T) (Matrix.toEuclideanLin T u)
            u).symm
      _ = inner ℝ (Matrix.toEuclideanLin T u) (Matrix.toEuclideanLin T u) := by rw [hadj]
      _ = ‖Matrix.toEuclideanLin T u‖ ^ 2 := by
          simpa using inner_self_eq_norm_sq (𝕜 := ℝ) (x := Matrix.toEuclideanLin T u)
  have hnorm : ∀ u : EuclideanSpace ℝ (Fin d),
      Real.sqrt (inner ℝ u (Matrix.toEuclideanLin S⁻¹ u)) = ‖Matrix.toEuclideanLin T u‖ := by
    intro u
    rw [hkey u, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm (x + y), hnorm x, hnorm y, map_add]
  exact norm_add_le _ _
