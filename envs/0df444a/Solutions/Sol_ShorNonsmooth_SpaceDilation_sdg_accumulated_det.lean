-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.sdg_accumulated_det
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:36:55.943219+00:00
-- url     : https://prove2.me/submissions/ae30fbc6-bbde-4f57-a653-9d409c58abcf

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

set_option autoImplicit false

open ShorNonsmooth.SpaceDilation in
theorem sdg16_dilation_apply {n : ℕ} (α : ℝ) (ξ x : EuclideanSpace ℝ (Fin n)) :
    dilation α ξ x = x + ((α - 1) * inner ℝ x ξ) • ξ := by
  have hi : (innerSL ℝ ξ) x = inner ℝ x ξ := by
    rw [real_inner_comm]; rfl
  simp only [dilation, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, hi]
  module

open ShorNonsmooth.SpaceDilation in
theorem sdg16_dilation_inv {n : ℕ} (α : ℝ) (hα : α ≠ 0) (ξ : EuclideanSpace ℝ (Fin n))
    (hξ : ‖ξ‖ = 1) (x : EuclideanSpace ℝ (Fin n)) :
    dilation (1 / α) ξ (dilation α ξ x) = x := by
  rw [sdg16_dilation_apply, sdg16_dilation_apply]
  have hξξ : inner ℝ ξ ξ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hξ]; norm_num
  rw [inner_add_left, real_inner_smul_left, hξξ, add_assoc, ← add_smul]
  have : (α - 1) * inner ℝ x ξ +
      (1 / α - 1) * (inner ℝ x ξ + (α - 1) * inner ℝ x ξ * 1) = 0 := by
    field_simp
    ring
  rw [this, zero_smul, add_zero]

open ShorNonsmooth.SpaceDilation in
theorem sdg16_adjoint_injective {n : ℕ}
    (B A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hBA : ∀ y, B (A y) = y) (v : EuclideanSpace ℝ (Fin n))
    (hv : ContinuousLinearMap.adjoint B v = 0) : v = 0 := by
  have h1 : inner ℝ (ContinuousLinearMap.adjoint B v) (A v) = inner ℝ v (B (A v)) :=
    ContinuousLinearMap.adjoint_inner_left B (A v) v
  rw [hv, inner_zero_left, hBA] at h1
  exact inner_self_eq_zero.mp h1.symm

open ShorNonsmooth.SpaceDilation in
theorem sdg16_invariant {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hα : ∀ k : ℕ, 1 ≤ k → α k ≠ 0) (k : ℕ) :
    ∀ y, (sdg g h α x₀ B₀ k).B ((sdg g h α x₀ B₀ k).A y) = y := by
  induction k with
  | zero =>
    intro y
    simp [sdg]
  | succ k ih =>
    intro y
    simp only [sdg, sdgStep]
    split_ifs with hg
    · exact ih y
    · simp only [ContinuousLinearMap.comp_apply]
      set s := sdg g h α x₀ B₀ k
      set w := ContinuousLinearMap.adjoint s.B (g s.x)
      have hw : w ≠ 0 := fun h0 => hg (sdg16_adjoint_injective s.B s.A ih _ h0)
      have hξ : ‖‖w‖⁻¹ • w‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)
      rw [sdg16_dilation_inv _ (hα (k + 1) (by omega)) _ hξ]
      exact ih y


open ShorNonsmooth.SpaceDilation in
theorem sdg16_dilation_det {n : ℕ} (α : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1) :
    LinearMap.det (dilation α ξ).toLinearMap = α := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b (dilation α ξ).toLinearMap =
      1 + Matrix.replicateCol Unit (fun i => (α - 1) * ξ i) *
        Matrix.replicateRow Unit (fun j => ξ j) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [b, ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, sdg16_dilation_apply, EuclideanSpace.inner_single_left,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply,
      Finset.univ_unique, Finset.sum_singleton, PiLp.single_apply]
    simp
    ring
  have hs : ∑ j, ξ j * ξ j = 1 := by
    have h1 : inner ℝ ξ ξ = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hξ]; norm_num
    rw [PiLp.inner_apply] at h1
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h1
    simp [sq]
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct]
  have : ∑ j, ξ j * ((α - 1) * ξ j) = (α - 1) * ∑ j, ξ j * ξ j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, hs]; ring

open ShorNonsmooth.SpaceDilation in
theorem sdg16_det {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hα : ∀ k : ℕ, 1 ≤ k → α k ≠ 0) (k : ℕ)
    (hstop : ∀ j : ℕ, j < k → g (sdg g h α x₀ B₀ j).x ≠ 0) :
    LinearMap.det (sdg g h α x₀ B₀ k).A.toLinearMap =
      (∏ j ∈ Finset.Icc 1 k, α j) *
        LinearMap.det (B₀.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap := by
  induction k with
  | zero => simp [sdg]
  | succ k ih =>
    have ih' := ih (fun j hj => hstop j (by omega))
    have hg : g (sdg g h α x₀ B₀ k).x ≠ 0 := hstop k (by omega)
    simp only [sdg, sdgStep, if_neg hg]
    set s := sdg g h α x₀ B₀ k with hs
    set w := ContinuousLinearMap.adjoint s.B (g s.x)
    have hw : w ≠ 0 := fun h0 =>
      hg (sdg16_adjoint_injective s.B s.A (sdg16_invariant g h α x₀ B₀ hα k) _ h0)
    have hξ : ‖‖w‖⁻¹ • w‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)
    rw [show ((dilation (α (k + 1)) (‖w‖⁻¹ • w)).comp s.A).toLinearMap =
        (dilation (α (k + 1)) (‖w‖⁻¹ • w)).toLinearMap.comp s.A.toLinearMap from rfl,
      LinearMap.det_comp, sdg16_dilation_det _ _ hξ, ih',
      Finset.prod_Icc_succ_top (by omega)]
    ring

open ShorNonsmooth.SpaceDilation in
theorem solution {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : 0 < δ)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k)
    (k : ℕ) (hstop : ∀ j : ℕ, j < k → g (sdg g h α x₀ B₀ j).x ≠ 0) :
    LinearMap.det (sdg g h α x₀ B₀ k).A.toLinearMap =
      (∏ j ∈ Finset.Icc 1 k, α j) *
        LinearMap.det (B₀.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap := by
  have hα' : ∀ k : ℕ, 1 ≤ k → α k ≠ 0 := fun k hk => by
    have := hα k hk; linarith
  exact sdg16_det g h α x₀ B₀ hα' k hstop
