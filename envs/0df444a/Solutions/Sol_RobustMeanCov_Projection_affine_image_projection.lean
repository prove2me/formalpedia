-- Prove2me | solution 1 for RobustMeanCov.Projection.affine_image_projection
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:39:08.731177+00:00
-- url     : https://prove2.me/submissions/c8a61990-ad06-4610-8d77-8fade7acd792

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

theorem aux_aip_selfadj {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (x Z : EuclideanSpace ℝ (Fin n)) :
    ⟪x, toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z⟫ = ⟪toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x, Z⟫ := by
  have hA : IsSelfAdjoint (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) :=
    (CFC.sqrt_nonneg S).isSelfAdjoint.map _
  rw [← ContinuousLinearMap.adjoint_inner_left, hA.adjoint_eq]

end RobustMeanCov.Projection

open RobustMeanCov.Projection

theorem solution {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hq : 0 < x.ofLp ⬝ᵥ S *ᵥ x.ofLp)
    (Z : EuclideanSpace ℝ (Fin n)) :
    let y : EuclideanSpace ℝ (Fin n) :=
      (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (-(1 / 2 : ℝ)) • toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x
    ⟪x, μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z⟫ =
      ⟪x, μ⟫ + (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (1 / 2 : ℝ) * ⟪y, Z⟫ := by
  intro y
  have h1 : (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (1 / 2 : ℝ) * (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hq]; norm_num
  simp only [y, inner_add_right, real_inner_smul_left, aux_aip_selfadj]
  rw [← mul_assoc, h1, one_mul]
