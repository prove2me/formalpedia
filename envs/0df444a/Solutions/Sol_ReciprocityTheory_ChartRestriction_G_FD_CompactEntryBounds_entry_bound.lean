-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:13.198749+00:00
-- url     : https://prove2.me/submissions/45a55bd6-2dfd-4d4c-ac6a-5b5e2d358d9c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace CompactEntryBounds
open Matrix NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private theorem gram_eq_transpose_mul_map_mul_fundamental_domains (τ : E →+* ℂ) (Y : Matrix (Fin r) (Fin r) ℂ) :
    gram τ X.Gm Y = Yᵀ * X.Gm.map τ * (Yᴴ)ᵀ := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul, Complex.star_def]
  exact Finset.sum_comm
end CompactEntryBounds
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
open Matrix NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
theorem _root_.solution {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0)
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (l b : Fin r) :
    ‖Y l b‖ ≤ ∑ k, ‖(X.Gm.map τ)⁻¹ k l‖ * ‖Y⁻¹ b k‖ := by
  set d : Fin r → ℂ := fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hd_def
  have hA : (X.Gm.map τ).det ≠ 0 := by
    have h := RingHom.map_det τ X.Gm
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (map_ne_zero τ).2 X.Gm_det
  have e1 : Yᵀ * X.Gm.map τ * (Yᴴ)ᵀ = diagonal d := by
    rw [← gram_eq_transpose_mul_map_mul_fundamental_domains, hg]
  have e2 := congrArg Matrix.transpose e1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    ← Matrix.mul_assoc] at e2
  have hYH : IsUnit (Yᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.2 (star_ne_zero.2 hY)
  have hAT : IsUnit (X.Gm.map τ)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 hA
  have e3 : Y = ((X.Gm.map τ)ᵀ)⁻¹ * (Yᴴ)⁻¹ * diagonal d := by
    rw [← e2]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc ((X.Gm.map τ)ᵀ)⁻¹ (Yᴴ)⁻¹ Yᴴ, Matrix.nonsing_inv_mul _ hYH, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hAT, Matrix.one_mul]
  have e4 : Y l b = (∑ k, (X.Gm.map τ)⁻¹ k l * star (Y⁻¹ b k)) * d b := by
    conv_lhs => rw [e3]
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply, ← Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_apply]
  have hdb : ‖d b‖ = 1 := by
    rw [hd_def, Complex.norm_real]
    unfold sgn
    split_ifs <;> norm_num
  rw [e4, norm_mul, hdb, mul_one]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, norm_star]
end ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
