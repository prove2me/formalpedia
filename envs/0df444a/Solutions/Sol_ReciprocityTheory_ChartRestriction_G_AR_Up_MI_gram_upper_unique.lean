-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.gram_upper_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:42.610047+00:00
-- url     : https://prove2.me/submissions/48274166-4899-4f30-b294-2dccf17d1145

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}
private lemma blockTriangular_inv_of_det_ne_zero {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.BlockTriangular id)
    (hd : M.det ≠ 0) : M⁻¹.BlockTriangular id := by
  letI := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hd)
  exact Matrix.blockTriangular_inv_of_blockTriangular hM
private lemma eq_of_mul_mul_eq_of_det_ne_zero {P Q X Y : Matrix (Fin n) (Fin n) ℂ} (hP : P.det ≠ 0) (hQ : Q.det ≠ 0)
    (h : P * X * Q = P * Y * Q) : X = Y := by
  have hP' := isUnit_iff_ne_zero.mpr hP
  have hQ' := isUnit_iff_ne_zero.mpr hQ
  have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z = P⁻¹ * (P * Z * Q) * Q⁻¹ := by
    intro Z
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP', Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ', Matrix.mul_one]
  calc X = P⁻¹ * (P * X * Q) * Q⁻¹ := e X
    _ = P⁻¹ * (P * Y * Q) * Q⁻¹ := by rw [h]
    _ = Y := (e Y).symm
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {ε : Fin n → ℂ} (hε : ∀ a, ε a * ε a = 1)
    {β β' : Matrix (Fin n) (Fin n) ℂ} (hβ : β.BlockTriangular id) (hβ' : β'.BlockTriangular id)
    (hd : β.det ≠ 0) (hd' : β'.det ≠ 0)
    (h : β'ᵀ * diagonal ε * β'.map (starRingEnd ℂ) = βᵀ * diagonal ε * β.map (starRingEnd ℂ)) :
    ∃ D : Fin n → ℂ, (∀ a, ‖D a‖ = 1) ∧ β' = diagonal D * β := by
  classical
  have hε0 : ∀ a, ε a ≠ 0 := fun a h0 => by
    have := hε a
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hu := isUnit_iff_ne_zero.mpr hd
  obtain ⟨γ, hγdef⟩ : ∃ γ : Matrix (Fin n) (Fin n) ℂ, γ = β' * β⁻¹ := ⟨_, rfl⟩
  have hγ : γ.BlockTriangular id := hγdef ▸ hβ'.mul (blockTriangular_inv_of_det_ne_zero hβ hd)
  have hγβ : β' = γ * β := by
    rw [hγdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  have hγd : γ.det ≠ 0 := by
    intro h0
    apply hd'
    rw [hγβ, Matrix.det_mul, h0, zero_mul]
  have hbar : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := fun M => by
    rw [RingHom.map_det]; rfl

  have key : γᵀ * diagonal ε * γ.map (starRingEnd ℂ) = diagonal ε := by
    apply eq_of_mul_mul_eq_of_det_ne_zero (P := βᵀ) (Q := β.map (starRingEnd ℂ))
    · rwa [Matrix.det_transpose]
    · rw [hbar]; exact (map_ne_zero _).mpr hd
    · rw [← h, hγβ, Matrix.transpose_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
  have hγinv := blockTriangular_inv_of_det_ne_zero hγ hγd
  have hγtu : IsUnit γᵀ.det := by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hγd

  have key2 : diagonal ε * γ.map (starRingEnd ℂ) = (γ⁻¹)ᵀ * diagonal ε := by
    rw [Matrix.transpose_nonsing_inv]
    conv_rhs => rw [← key]
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγtu, Matrix.one_mul]
  have hoff : ∀ i j, i ≠ j → γ i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have e := congrFun (congrFun key2 i) j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, hγinv hlt, zero_mul,
        Matrix.map_apply] at e
      exact (map_eq_zero _).mp ((mul_eq_zero.mp e).resolve_left (hε0 i))
    · exact hγ hlt
  have hγdiag : γ = diagonal (fun a => γ a a) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  refine ⟨fun a => γ a a, fun a => ?_, by rw [← hγdiag]; exact hγβ⟩
  have e := congrFun (congrFun key a) a
  rw [hγdiag] at e
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at e
  have h2 : γ a a * starRingEnd ℂ (γ a a) = 1 := by
    have : ε a * (γ a a * starRingEnd ℂ (γ a a)) = ε a * 1 := by linear_combination e
    exact mul_left_cancel₀ (hε0 a) this
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖γ a a‖ ^ 2 = 1 := by exact_mod_cast h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h3
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
