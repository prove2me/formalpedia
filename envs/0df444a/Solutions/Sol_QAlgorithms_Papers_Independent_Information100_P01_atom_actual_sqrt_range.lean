-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P01.atom_actual_sqrt_range
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T12:16:47.588996+00:00
-- url     : https://prove2.me/submissions/bb2f4fb5-61e2-48bf-9068-991aa86719ed

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P01

set_option autoImplicit false

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P01.Aux7526

/-- Douglas-type lemma: if `‖⟪y, z⟫‖ ≤ ‖S z‖` for all `z`, with `S` self-adjoint, then
`y = S x` for some `x` orthogonal to `ker S` with `‖x‖ ≤ 1`. -/
theorem douglas {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (y : H)
    (hb : ∀ z : H, ‖inner ℂ y z‖ ≤ ‖S z‖) :
    ∃ x : H, (∀ z : H, S z = 0 → inner ℂ z x = 0) ∧ ‖x‖ ≤ 1 ∧ S x = y := by
  set Sl : H →ₗ[ℂ] H := (S : H →ₗ[ℂ] H) with hSl
  set φ : H →ₗ[ℂ] ℂ := (innerSL ℂ y).toLinearMap with hφ
  have hker : LinearMap.ker Sl ≤ LinearMap.ker φ := by
    intro z hz
    simp only [LinearMap.mem_ker] at hz ⊢
    have h1 := hb z
    have : S z = 0 := hz
    rw [this, norm_zero] at h1
    have h2 : inner ℂ y z = 0 := norm_le_zero_iff.mp h1
    simpa [hφ] using h2
  set ψ : LinearMap.range Sl →ₗ[ℂ] ℂ :=
    ((LinearMap.ker Sl).liftQ φ hker).comp (Sl.quotKerEquivRange.symm : _ →ₗ[ℂ] _) with hψ
  have hψapp : ∀ z : H, ψ ⟨Sl z, LinearMap.mem_range_self Sl z⟩ = inner ℂ y z := by
    intro z
    simp only [hψ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    simp [hφ]
  have hψb : ∀ w : LinearMap.range Sl, ‖ψ w‖ ≤ 1 * ‖w‖ := by
    rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hw
    rw [hψapp z, one_mul]
    exact hb z
  set f : StrongDual ℂ (LinearMap.range Sl) := ψ.mkContinuous 1 hψb with hf
  obtain ⟨g, hgf, hgn⟩ := exists_extension_norm_eq (LinearMap.range Sl) f
  have hfn : ‖f‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  set x0 : H := (InnerProductSpace.toDual ℂ H).symm g with hx0
  have hx0n : ‖x0‖ ≤ 1 := by
    rw [hx0, LinearIsometryEquiv.norm_map, hgn]; exact hfn
  have hx0S : ∀ z : H, inner ℂ x0 (S z) = inner ℂ y z := by
    intro z
    rw [hx0, InnerProductSpace.toDual_symm_apply]
    have := hgf ⟨Sl z, LinearMap.mem_range_self Sl z⟩
    simp only at this
    rw [show S z = Sl z from rfl, this, hf, LinearMap.mkContinuous_apply, hψapp]
  have hsym := hS.isSymmetric
  have hSx0 : S x0 = y := by
    apply ext_inner_right ℂ
    intro z
    rw [← hx0S z]
    exact hsym x0 z
  set K : Submodule ℂ H := LinearMap.ker Sl with hK
  have : CompleteSpace K := (ContinuousLinearMap.isClosed_ker S).completeSpace_coe
  set x : H := x0 - K.starProjection x0 with hx
  have hxK : x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x0
  have hpK : K.starProjection x0 ∈ K := K.starProjection_apply_mem x0
  refine ⟨x, ?_, ?_, ?_⟩
  · intro z hz
    exact Submodule.inner_right_of_mem_orthogonal (K := K) (by simpa [hK, hSl] using hz) hxK
  · have h1 : inner ℂ x (K.starProjection x0) = 0 :=
      Submodule.inner_left_of_mem_orthogonal (K := K) hpK hxK
    have h2 : ‖x‖ ^ 2 = (inner ℂ x x0).re := by
      have : inner ℂ x x0 = inner ℂ x x + inner ℂ x (K.starProjection x0) := by
        rw [← inner_add_right, hx, sub_add_cancel]
      rw [this, h1, add_zero, inner_self_eq_norm_sq_to_K]
      norm_cast
    have h3 : (inner ℂ x x0).re ≤ ‖x‖ * ‖x0‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm x x0)
    by_cases hx0' : ‖x‖ = 0
    · rw [hx0']; exact zero_le_one
    · have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0')
      have : ‖x‖ ≤ ‖x0‖ := by nlinarith
      linarith
  · have : S (K.starProjection x0) = 0 := hpK
    rw [hx, map_sub, this, sub_zero, hSx0]

end QAlgorithms.Papers.Independent.Information100.P01.Aux7526

open QAlgorithms.Papers.Independent.Information100.P01 in
theorem solution
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [Countable I]
    (b : HilbertBasis I ℂ H) (rho : H →L[ℂ] H)
    (hrho : IsTraceOneOperator b rho) (y : H)
    (hdom : ∀ z : H, ‖inner ℂ y z‖ ^ 2 ≤ (inner ℂ z (rho z)).re) :
    ∃ x : H,
      (∀ z : H, rho z = 0 → inner ℂ z x = 0) ∧
      ‖x‖ ≤ 1 ∧ CFC.sqrt rho x = y ∧
      (y ≠ 0 → ∃ u : H,
        (∀ z : H, rho z = 0 → inner ℂ z u = 0) ∧
        CFC.sqrt rho u = (‖y‖⁻¹ : ℂ) • y ∧
        ‖y‖ ^ 2 * ‖u‖ ^ 2 ≤ 1) := by
  have hpos : 0 ≤ rho := (ContinuousLinearMap.nonneg_iff_isPositive rho).mpr hrho.1
  set S : H →L[ℂ] H := CFC.sqrt rho with hSdef
  have hSsa : IsSelfAdjoint S := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg rho)
  have hSS : S * S = rho := CFC.sqrt_mul_sqrt_self rho hpos
  have hquad : ∀ z : H, (inner ℂ z (rho z)).re = ‖S z‖ ^ 2 := by
    intro z
    have : rho z = S (S z) := by rw [← hSS]; rfl
    have e : inner ℂ (S z) (S z) = inner ℂ z (S (S z)) := hSsa.isSymmetric z (S z)
    rw [this, ← e, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hb : ∀ z : H, ‖inner ℂ y z‖ ≤ ‖S z‖ := by
    intro z
    have h := hdom z
    rw [hquad z] at h
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  have hkr : ∀ z : H, rho z = 0 → S z = 0 := by
    intro z hz
    have h := hquad z
    rw [hz, inner_zero_right, Complex.zero_re] at h
    have : ‖S z‖ = 0 := by nlinarith [norm_nonneg (S z)]
    exact norm_eq_zero.mp this
  obtain ⟨x, hxk, hxn, hxS⟩ := Aux7526.douglas S hSsa y hb
  refine ⟨x, fun z hz => hxk z (hkr z hz), hxn, hxS, ?_⟩
  intro hy
  refine ⟨(‖y‖⁻¹ : ℂ) • x, ?_, ?_, ?_⟩
  · intro z hz
    rw [inner_smul_right, hxk z (hkr z hz), mul_zero]
  · rw [map_smul, hxS]
  · have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm, mul_pow,
      ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hyn), one_mul]
    nlinarith [norm_nonneg x]

end
