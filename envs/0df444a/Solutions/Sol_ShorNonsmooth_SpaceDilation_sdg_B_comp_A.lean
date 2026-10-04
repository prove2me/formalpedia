-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.sdg_B_comp_A
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:46:37.455858+00:00
-- url     : https://prove2.me/submissions/50d9919a-bf57-4a5e-9b71-17399032e493

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

set_option autoImplicit false

open ShorNonsmooth.SpaceDilation in
theorem sdgBA_dilation_apply {n : ℕ} (α : ℝ) (ξ x : EuclideanSpace ℝ (Fin n)) :
    dilation α ξ x = x + ((α - 1) * inner ℝ ξ x) • ξ := by
  simp only [dilation, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply]
  module

open ShorNonsmooth.SpaceDilation in
theorem sdgBA_dilation_inv_apply {n : ℕ} (α : ℝ) (hα : α ≠ 0) (ξ x : EuclideanSpace ℝ (Fin n))
    (hξ : ‖ξ‖ = 1) : dilation (1 / α) ξ (dilation α ξ x) = x := by
  rw [sdgBA_dilation_apply, sdgBA_dilation_apply, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, hξ]
  have : ((1 / α - 1) * (inner ℝ ξ x + (α - 1) * inner ℝ ξ x * 1 ^ 2)) = -((α - 1) * inner ℝ ξ x) := by
    field_simp
    ring
  rw [add_assoc, ← add_smul, this, add_neg_cancel, zero_smul, add_zero]

open ShorNonsmooth.SpaceDilation in
theorem sdgBA_key {n : ℕ}
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
      rw [sdgBA_dilation_inv_apply _ (hα k) _ _ hn, ih]

open ShorNonsmooth.SpaceDilation in
theorem solution {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : 0 < δ)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k)
    (k : ℕ) (hstop : ∀ j : ℕ, j < k → g (sdg g h α x₀ B₀ j).x ≠ 0) :
    ((sdg g h α x₀ B₀ k).B.toLinearMap).comp ((sdg g h α x₀ B₀ k).A.toLinearMap) =
      LinearMap.id := by
  have hα' : ∀ k : ℕ, α (k + 1) ≠ 0 := fun k => by
    have := hα (k + 1) (by omega)
    exact ne_of_gt (by linarith)
  exact LinearMap.ext fun x => sdgBA_key g h α x₀ B₀ hα' k x
