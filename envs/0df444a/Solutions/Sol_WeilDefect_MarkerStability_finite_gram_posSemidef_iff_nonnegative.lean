-- Prove2me | solution 1 for WeilDefect.MarkerStability.finite_gram_posSemidef_iff_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T21:08:26.569796+00:00
-- url     : https://prove2.me/submissions/62c8d30e-b64e-4ba3-b9af-593b8a7b2258

import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
private theorem finite_operator_gram_quadratic
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Fintype I] (A : H →L[ℂ] H) (u : I → H) (a : I → ℂ) :
    star a ⬝ᵥ ((fun i j => ⟪u i, A (u j)⟫_ℂ) *ᵥ a) =
      ⟪∑ i, a i • u i, A (∑ i, a i • u i)⟫_ℂ := by
  simp only [dotProduct, Matrix.mulVec, map_sum, map_smul, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  change star (a j) * (⟪u j, A (u i)⟫_ℂ * a i) = a i * (star (a j) * ⟪u j, A (u i)⟫_ℂ)
  ring

/-- A finite Gram test is complete when the operator is a nonnegative scalar
on the orthogonal complement of the column span. No invertibility, basis,
strict spectral gap or linear independence is assumed. -/
theorem solution
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Fintype I] (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (u : I → H) (δ : ℝ) (hδ : 0 ≤ δ)
    (hshell : ∀ z : H, (∀ i : I, ⟪u i, z⟫_ℂ = 0) → A z = δ • z) :
    Matrix.PosSemidef (fun i j => ⟪u i, A (u j)⟫_ℂ) ↔ 0 ≤ A := by
  have hM : Matrix.IsHermitian (fun i j => ⟪u i, A (u j)⟫_ℂ) := by
    ext i j
    change star ⟪u j, A (u i)⟫_ℂ = ⟪u i, A (u j)⟫_ℂ
    rw [RCLike.star_def, inner_conj_symm]
    exact hA.isSymmetric _ _
  constructor
  · intro h
    let K := Submodule.span ℂ (Set.range u)
    letI : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
    have hspan : ∀ y : H, y ∈ K → 0 ≤ RCLike.re ⟪A y, y⟫_ℂ := by
      intro y hy
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp hy
      have hp := h.dotProduct_mulVec_nonneg a
      rw [finite_operator_gram_quadratic, ha] at hp
      exact (Complex.nonneg_iff.mp hp).1.trans_eq (inner_re_symm (𝕜 := ℂ) y (A y))
    apply (ContinuousLinearMap.nonneg_iff_isPositive (f := A)).mpr
    apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨hA, ?_⟩
    intro x
    let y := K.starProjection x
    let z := x - y
    have hy : y ∈ K := K.starProjection_apply_mem x
    have hz : z ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
    have hi : ⟪y, z⟫_ℂ = 0 := hz y hy
    have hi' : ⟪z, y⟫_ℂ = 0 := inner_eq_zero_symm.mpr hi
    have hAz : A z = δ • z := hshell z (fun i => hz (u i) (Submodule.subset_span ⟨i, rfl⟩))
    have hcross : ⟪A y, z⟫_ℂ = 0 := by
      have hsym : ⟪A y, z⟫_ℂ = ⟪y, A z⟫_ℂ := hA.isSymmetric y z
      rw [hsym, hAz]
      change ⟪y, (δ : ℂ) • z⟫_ℂ = 0
      rw [inner_smul_right, hi, mul_zero]
    have hcross' : ⟪A z, y⟫_ℂ = 0 := by
      rw [hAz]
      change ⟪(δ : ℂ) • z, y⟫_ℂ = 0
      rw [inner_smul_left, hi', mul_zero]
    have hzz : RCLike.re ⟪A z, z⟫_ℂ = δ * ‖z‖ ^ 2 := by
      rw [hAz]
      change RCLike.re ⟪(δ : ℂ) • z, z⟫_ℂ = _
      rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
      change (star (δ : ℂ) * (‖z‖ : ℂ) ^ 2).re = _
      simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    have hx : x = y + z := by dsimp [z]; abel
    change 0 ≤ RCLike.re ⟪A x, x⟫_ℂ
    rw [hx]
    simp only [map_add, inner_add_left, inner_add_right, hcross, hcross',
      add_zero, zero_add, map_add, hzz]
    exact add_nonneg (hspan y hy) (mul_nonneg hδ (sq_nonneg ‖z‖))
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM
    intro a
    rw [finite_operator_gram_quadratic]
    exact ((ContinuousLinearMap.nonneg_iff_isPositive (f := A)).mp h).inner_nonneg_right _
