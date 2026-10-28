-- Prove2me | solution 1 for QuantumSDP18.MeasureBE.eq_14_iff_specNorm
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:11:55.550314+00:00
-- url     : https://prove2.me/submissions/c14b7cba-a6d6-4df7-b12d-f3cf6253b02f

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_MeasureBE_Setting

namespace Aux_QSDP_14

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_eq_sum_inner {κ : Type*} [Fintype κ] (A : Matrix ι ι ℂ) (B : Matrix κ ι ℂ) :
    (A * (B.conjTranspose * B)).trace =
      ∑ k, inner ℂ (WithLp.toLp 2 (star (B k)) : EuclideanSpace ℂ ι)
        (toEuclideanCLM (n := ι) (𝕜 := ℂ) A (WithLp.toLp 2 (star (B k)))) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanCLM,
    star_star, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct,
    mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  have h1 : ∀ i, (∑ j, ∑ k, A i j * (star (B k j) * B k i)) =
      ∑ k, ∑ j, A i j * (star (B k j) * B k i) := fun i => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma sum_norm_sq {κ : Type*} [Fintype κ] (B : Matrix κ ι ℂ) :
    ((∑ k, ‖(WithLp.toLp 2 (star (B k)) : EuclideanSpace ℂ ι)‖ ^ 2 : ℝ) : ℂ) =
      (B.conjTranspose * B).trace := by
  simp only [EuclideanSpace.norm_sq_eq, WithLp.toLp, Pi.star_apply, norm_star]
  push_cast
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.mul_conj', mul_comm]
  rfl

lemma inner_le (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    ‖inner ℂ x (toEuclideanCLM (n := ι) (𝕜 := ℂ) A x)‖ ≤ ‖A‖ * ‖x‖ ^ 2 := by
  refine le_trans (norm_inner_le_norm _ _) ?_
  have := (toEuclideanCLM (n := ι) (𝕜 := ℂ) A).le_opNorm x
  rw [l2_opNorm_toEuclideanCLM] at this
  nlinarith [norm_nonneg x]

end Aux_QSDP_14

open Matrix Aux_QSDP_14 QuantumSDP18.MeasureBE in
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℕ)
    (U : Matrix (ι × Anc c) (ι × Anc c) ℂ) (M : Matrix ι ι ℂ) (ε : ℝ)
    (hM : M.IsHermitian) (hε : 0 ≤ ε) :
    (∀ ρ : Matrix ι ι ℂ, IsDensity ρ → ‖((blockK c U - M) * ρ).trace‖ ≤ ε) ↔
      QAlgorithms.specNorm (blockK c U - M) ≤ ε := by
  obtain ⟨A, hAd⟩ : ∃ A, A = blockK c U - M := ⟨_, rfl⟩
  rw [← hAd]
  have hK : (blockK c U).IsHermitian := by
    unfold blockK IsHermitian
    have hP : (accProj (ι := ι) c).conjTranspose = accProj c := by
      unfold accProj
      rw [diagonal_conjTranspose]
      congr 1
      funext x
      simp only [Pi.star_apply]
      split_ifs <;> simp
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP, Matrix.mul_assoc]
  have hA : A.IsHermitian := by rw [hAd]; exact hK.sub hM
  have hnorm : QAlgorithms.specNorm A = ‖A‖ := rfl
  rw [hnorm]
  constructor
  · intro h
    have hsym : (toEuclideanCLM (n := ι) (𝕜 := ℂ) A).IsSymmetric := by
      rw [coe_toEuclideanCLM_eq_toEuclideanLin]
      exact (isHermitian_iff_isSymmetric).mp hA
    rw [← l2_opNorm_toEuclideanCLM, ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hsym]
    apply ciSup_le
    intro x
    by_cases hx : x = 0
    · rw [hx, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero]; exact hε
    have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hc : ((‖x‖⁻¹ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact inv_ne_zero hxn
    rw [← ContinuousLinearMap.rayleigh_smul _ x hc]
    set y := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hy
    have hy1 : ‖y‖ = 1 := by
      rw [hy, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ hxn]
    -- density matrix from y
    let B : Matrix Unit ι ℂ := fun _ j => star (WithLp.ofLp y j)
    have hBk : ∀ k, (WithLp.toLp 2 (star (B k)) : EuclideanSpace ℂ ι) = y := by
      intro k
      ext j
      simp [B]
    have hdens : IsDensity (B.conjTranspose * B) := by
      refine ⟨posSemidef_conjTranspose_mul_self B, ?_⟩
      rw [← sum_norm_sq]
      simp [hBk, hy1]
    have hρ := h _ hdens
    rw [trace_eq_sum_inner] at hρ
    simp only [hBk, Finset.univ_unique, Finset.sum_singleton] at hρ
    unfold ContinuousLinearMap.rayleighQuotient ContinuousLinearMap.reApplyInnerSelf
    rw [hy1, one_pow, div_one]
    refine le_trans (RCLike.abs_re_le_norm _) ?_
    rw [norm_inner_symm]
    exact hρ
  · intro h ρ hρ
    obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.1.nonneg
    rw [Matrix.star_eq_conjTranspose] at hρ ⊢
    rw [trace_eq_sum_inner]
    have hsum := sum_norm_sq B
    rw [hρ.2] at hsum
    have hs1 : ∑ k, ‖(WithLp.toLp 2 (star (B k)) : EuclideanSpace ℂ ι)‖ ^ 2 = 1 := by
      exact_mod_cast hsum
    calc ‖∑ k, inner ℂ (WithLp.toLp 2 (star (B k)) : EuclideanSpace ℂ ι)
          (toEuclideanCLM (n := ι) (𝕜 := ℂ) A (WithLp.toLp 2 (star (B k))))‖
        ≤ ∑ k, ‖inner ℂ (WithLp.toLp 2 (star (B k)) : EuclideanSpace ℂ ι)
          (toEuclideanCLM (n := ι) (𝕜 := ℂ) A (WithLp.toLp 2 (star (B k))))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k, ‖A‖ * ‖(WithLp.toLp 2 (star (B k)) : EuclideanSpace ℂ ι)‖ ^ 2 :=
          Finset.sum_le_sum fun k _ => inner_le A _
      _ = ‖A‖ := by rw [← Finset.mul_sum, hs1, mul_one]
      _ ≤ ε := h
