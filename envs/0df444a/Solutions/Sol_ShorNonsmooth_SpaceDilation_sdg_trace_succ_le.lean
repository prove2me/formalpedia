-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.sdg_trace_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:48:48.894349+00:00
-- url     : https://prove2.me/submissions/13dbb5c8-ced1-4431-a51c-41f996f65b28

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

set_option autoImplicit false

open ShorNonsmooth.SpaceDilation in
theorem sdgTr_dilation_apply {n : ℕ} (α : ℝ) (ξ x : EuclideanSpace ℝ (Fin n)) :
    dilation α ξ x = x + ((α - 1) * inner ℝ ξ x) • ξ := by
  simp only [dilation, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply]
  module

open ShorNonsmooth.SpaceDilation in
theorem sdgTr_dilation_inv_apply {n : ℕ} (α : ℝ) (hα : α ≠ 0) (ξ x : EuclideanSpace ℝ (Fin n))
    (hξ : ‖ξ‖ = 1) : dilation (1 / α) ξ (dilation α ξ x) = x := by
  rw [sdgTr_dilation_apply, sdgTr_dilation_apply, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, hξ]
  have : ((1 / α - 1) * (inner ℝ ξ x + (α - 1) * inner ℝ ξ x * 1 ^ 2)) = -((α - 1) * inner ℝ ξ x) := by
    field_simp
    ring
  rw [add_assoc, ← add_smul, this, add_neg_cancel, zero_smul, add_zero]

open ShorNonsmooth.SpaceDilation in
theorem sdgTr_key {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hα : ∀ k : ℕ, α (k + 1) ≠ 0) (k : ℕ) :
    ∀ x, (sdg g h α x₀ B₀ k).B ((sdg g h α x₀ B₀ k).A x) = x := by
  induction k with
  | zero => intro x; simp [sdg]
  | succ k ih =>
    intro x
    show (sdgStep g h α k (sdg g h α x₀ B₀ k)).B ((sdgStep g h α k (sdg g h α x₀ B₀ k)).A x) = x
    set s := sdg g h α x₀ B₀ k with hs
    unfold sdgStep
    split_ifs with hg
    · exact ih x
    · set v := ContinuousLinearMap.adjoint s.B (g s.x) with hv
      have hv0 : v ≠ 0 := by
        intro h0
        apply hg
        have h1 : inner ℝ v (s.A (g s.x)) = inner ℝ (g s.x) (g s.x) := by
          rw [hv, ContinuousLinearMap.adjoint_inner_left, ih]
        rw [h0, inner_zero_left] at h1
        exact inner_self_eq_zero.mp h1.symm
      have hn : ‖‖v‖⁻¹ • v‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)
      simp only [ContinuousLinearMap.comp_apply]
      rw [sdgTr_dilation_inv_apply _ (hα k) _ _ hn, ih]

theorem sdgTr_trace_eq {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        ((LinearMap.adjoint A.toLinearMap).comp A.toLinearMap) =
      ∑ i, ‖A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, ContinuousLinearMap.coe_coe,
    real_inner_self_eq_norm_sq]

open ShorNonsmooth.SpaceDilation in
theorem sdgTr_dilation_norm_sq {n : ℕ} (a : ℝ) (ξ y : EuclideanSpace ℝ (Fin n))
    (hξ : ‖ξ‖ = 1) :
    ‖dilation a ξ y‖ ^ 2 = ‖y‖ ^ 2 + (a ^ 2 - 1) * (inner ℝ ξ y) ^ 2 := by
  rw [sdgTr_dilation_apply, norm_add_sq_real, inner_smul_right, norm_smul, hξ,
    Real.norm_eq_abs, mul_one, sq_abs, real_inner_comm ξ y]
  ring

open ShorNonsmooth.SpaceDilation in
theorem solution {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (d αstar δ : ℝ) (hd : 0 < d) (hαstar : 0 < αstar) (hδ : 0 < δ)
    (hg : ∀ k : ℕ, ‖g (sdg g h α x₀ B₀ k).x‖ ≤ d)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k ∧ α k ≤ αstar)
    (k : ℕ) (hstop : ∀ j : ℕ, j ≤ k → g (sdg g h α x₀ B₀ j).x ≠ 0)
    (hgT : gTilde g h α x₀ B₀ k ≠ 0) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        ((LinearMap.adjoint (sdg g h α x₀ B₀ (k + 1)).A.toLinearMap).comp
          (sdg g h α x₀ B₀ (k + 1)).A.toLinearMap) ≤
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        ((LinearMap.adjoint (sdg g h α x₀ B₀ k).A.toLinearMap).comp
          (sdg g h α x₀ B₀ k).A.toLinearMap) +
        (αstar ^ 2 - 1) * d ^ 2 / ‖gTilde g h α x₀ B₀ k‖ ^ 2 := by
  have hα0 : ∀ j : ℕ, α (j + 1) ≠ 0 := fun j => by
    have := (hα (j + 1) (by omega)).1
    exact ne_of_gt (by linarith)
  have hBA := sdgTr_key g h α x₀ B₀ hα0 k
  set s := sdg g h α x₀ B₀ k with hs
  have hgx : g s.x ≠ 0 := hstop k le_rfl
  set v := gTilde g h α x₀ B₀ k with hv
  have hv' : v = ContinuousLinearMap.adjoint s.B (g s.x) := rfl
  set ξ := ‖v‖⁻¹ • v with hξdef
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hgT
  have hξ : ‖ξ‖ = 1 := by
    rw [hξdef, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hvn
  have hA1 : (sdg g h α x₀ B₀ (k + 1)).A = (dilation (α (k + 1)) ξ).comp s.A := by
    show (sdgStep g h α k s).A = _
    unfold sdgStep
    rw [if_neg hgx]
    rfl
  have hinner : ∀ y, inner ℝ ξ (s.A y) = ‖v‖⁻¹ * inner ℝ (g s.x) y := by
    intro y
    rw [hξdef, inner_smul_left, hv', ContinuousLinearMap.adjoint_inner_left, hBA]
    simp
  rw [hA1, sdgTr_trace_eq, sdgTr_trace_eq]
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hsum : ∑ i, ‖((dilation (α (k + 1)) ξ).comp s.A) (b i)‖ ^ 2 =
      ∑ i, ‖s.A (b i)‖ ^ 2 + (α (k + 1) ^ 2 - 1) * (‖v‖⁻¹ ^ 2 * ‖g s.x‖ ^ 2) := by
    simp_rw [ContinuousLinearMap.comp_apply, sdgTr_dilation_norm_sq _ _ _ hξ, hinner,
      Finset.sum_add_distrib, mul_pow, ← Finset.mul_sum]
    rw [b.sum_sq_inner_left]
  rw [hsum, add_le_add_iff_left]
  obtain ⟨ha1, ha2⟩ := hα (k + 1) (by omega)
  have hA : 0 ≤ α (k + 1) ^ 2 - 1 := by nlinarith
  have hB : α (k + 1) ^ 2 - 1 ≤ αstar ^ 2 - 1 := by nlinarith
  have hG : ‖g s.x‖ ^ 2 ≤ d ^ 2 := by
    have := hg k
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  rw [inv_pow, div_eq_mul_inv, ← mul_assoc]
  have hre : (α (k + 1) ^ 2 - 1) * (‖v‖ ^ 2)⁻¹ * ‖g s.x‖ ^ 2 =
      (α (k + 1) ^ 2 - 1) * ‖g s.x‖ ^ 2 * (‖v‖ ^ 2)⁻¹ := by ring
  rw [hre]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul hB hG (by positivity) (by nlinarith)
