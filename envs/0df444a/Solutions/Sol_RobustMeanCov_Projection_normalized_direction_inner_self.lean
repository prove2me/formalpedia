-- Prove2me | solution 1 for RobustMeanCov.Projection.normalized_direction_inner_self
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:35:19.849663+00:00
-- url     : https://prove2.me/submissions/8c9619e8-69f5-4040-96b6-b291159069d8

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

set_option backward.isDefEq.respectTransparency false in
theorem aux_ndis_sqrt_inner {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) :
    ⟪toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x, toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x⟫
      = x.ofLp ⬝ᵥ S *ᵥ x.ofLp := by
  rw [← ContinuousLinearMap.adjoint_inner_right, IsSelfAdjoint.adjoint_eq,
    ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    CFC.sqrt_mul_sqrt_self _ hS.nonneg, inner_toEuclideanCLM]
  exact (CFC.sqrt_nonneg S).isSelfAdjoint.map _

end RobustMeanCov.Projection

open RobustMeanCov.Projection
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

theorem solution {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hq : 0 < x.ofLp ⬝ᵥ S *ᵥ x.ofLp) :
    let y : EuclideanSpace ℝ (Fin n) :=
      (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (-(1 / 2 : ℝ)) • toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x
    ⟪y, y⟫ = 1 := by
  intro y
  simp only [y, inner_smul_left, inner_smul_right, aux_ndis_sqrt_inner x S hS]
  set q := x.ofLp ⬝ᵥ S *ᵥ x.ofLp with hqdef
  simp only [conj_trivial]
  rw [← mul_assoc, ← Real.rpow_add hq]
  norm_num
  rw [Real.rpow_neg_one]
  exact inv_mul_cancel₀ hq.ne'
