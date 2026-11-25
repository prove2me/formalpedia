-- Prove2me | solution 1 for SSLWithoutPairs.predictor_fixed_point_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:56:15.057612+00:00
-- url     : https://prove2.me/submissions/7ca8e320-b917-4f0f-9df8-935928decfc5

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Matrix
namespace SSLWithoutPairs

theorem predictor_fixed_point_symmetric {d n₁ : ℕ} (αp σ η τ : ℝ) (hαp : 0 < αp) (hη : 0 < η)
    (W : Matrix (Fin d) (Fin n₁) ℝ) (Wp : Matrix (Fin d) (Fin d) ℝ)
    (hfix : isoFlowWp αp σ η τ Wp (W * Wᵀ) = 0) :
    Wpᵀ = Wp := by
  set F := W * Wᵀ with hF
  set c := αp * (1 + σ ^ 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hFt : Fᵀ = F := by rw [hF, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hFpsd : F.PosSemidef := by
    have := Matrix.posSemidef_self_mul_conjTranspose W
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set A := η • (1 : Matrix (Fin d) (Fin d) ℝ) + c • F with hA
  have hApd : A.PosDef := by
    have h1 : (η • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef := Matrix.PosDef.one.smul hη
    exact h1.add_posSemidef (hFpsd.smul hc0)
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.2 hApd.det_pos.ne'
  have hAt : Aᵀ = A := by
    rw [hA, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
      Matrix.transpose_one, hFt]
  have h1 : Wp * A = (αp * τ) • F := by
    have hf : -(αp * (1 + σ ^ 2)) • (Wp * F) + (αp * τ) • F - η • Wp = 0 := hfix
    rw [← sub_eq_zero, hA, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul]
    have e : η • Wp + c • (Wp * F) - (αp * τ) • F =
        -(-(αp * (1 + σ ^ 2)) • (Wp * F) + (αp * τ) • F - η • Wp) := by
      rw [hc]; module
    rw [e, hf, neg_zero]
  have hWp : Wp = (αp * τ) • (F * A⁻¹) := by
    calc Wp = Wp * A * A⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = (αp * τ) • (F * A⁻¹) := by rw [h1, Matrix.smul_mul]
  have hcomm : F * A = A * F := by
    rw [hA, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hcomm' : F * A⁻¹ = A⁻¹ * F := by
    calc F * A⁻¹ = A⁻¹ * (A * F) * A⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
      _ = A⁻¹ * (F * A) * A⁻¹ := by rw [hcomm]
      _ = A⁻¹ * F := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  rw [hWp, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hAt, hFt,
    hcomm']

end SSLWithoutPairs

open SSLWithoutPairs in
theorem solution {d n₁ : ℕ} (αp σ η τ : ℝ) (hαp : 0 < αp) (hη : 0 < η)
    (W : Matrix (Fin d) (Fin n₁) ℝ) (Wp : Matrix (Fin d) (Fin d) ℝ)
    (hfix : isoFlowWp αp σ η τ Wp (W * Wᵀ) = 0) :
    Wpᵀ = Wp :=
  SSLWithoutPairs.predictor_fixed_point_symmetric αp σ η τ hαp hη W Wp hfix
