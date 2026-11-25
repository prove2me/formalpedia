-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.posDef_norm_dot_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:46.107852+00:00
-- url     : https://prove2.me/submissions/4cf99278-0c32-4a25-b2d0-113c27d46bd5

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder
variable {X : Type*} [MeasurableSpace X]
private theorem dotProduct_eq_sum_mul {r : ℕ} (u v : Fin r → ℂ) : u ⬝ᵥ v = ∑ i, u i * v i := rfl
private theorem mulVec_apply_eq_sum_pluriharmonic_analysis {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) (i : Fin r) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl
private theorem isHermitian_of_posDef {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) : G.IsHermitian := by
  exact hG.1
private theorem posDef_inv_of_posDef {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) : G⁻¹.PosDef := by
  exact hG.inv
private theorem star_dotProduct_mulVec_pos_of_posDef {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) {u : Fin r → ℂ}
    (hu : u ≠ 0) : 0 < star u ⬝ᵥ G *ᵥ u := by
  first
  | exact hG.2 u hu
  | exact hG.dotProduct_mulVec_pos hu
private theorem re_pos_and_im_eq_zero_of_pos {z : ℂ} (h : 0 < z) : 0 < z.re ∧ z.im = 0 := by
  have h' := Complex.pos_iff.mp h
  exact ⟨h'.1, h'.2.symm⟩
private theorem re_star_dotProduct_mulVec_nonneg_of_posDef {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (u : Fin r → ℂ) :
    0 ≤ (star u ⬝ᵥ G *ᵥ u).re := by
  by_cases hu : u = 0
  · subst hu; simp
  · exact (re_pos_and_im_eq_zero_of_pos (star_dotProduct_mulVec_pos_of_posDef hG hu)).1.le
private theorem isUnit_det_of_posDef' {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) : IsUnit G.det := by
  exact (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
private theorem mul_inv_eq_one_of_posDef {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) : G * G⁻¹ = 1 :=
  Matrix.mul_nonsing_inv G (isUnit_det_of_posDef' hG)
private theorem inv_mul_eq_one_of_posDef {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) : G⁻¹ * G = 1 :=
  Matrix.nonsing_inv_mul G (isUnit_det_of_posDef' hG)
private theorem conj_star_dotProduct {r : ℕ} (u v : Fin r → ℂ) : starRingEnd ℂ (star u ⬝ᵥ v) = star v ⬝ᵥ u := by
  simp only [dotProduct_eq_sum_mul, Pi.star_apply, map_sum, map_mul, starRingEnd_apply, star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
private theorem star_mulVec_dotProduct_of_isHermitian {r : ℕ} {H : Matrix (Fin r) (Fin r) ℂ} (hH : H.IsHermitian)
    (u v : Fin r → ℂ) : star (H *ᵥ u) ⬝ᵥ v = star u ⬝ᵥ H *ᵥ v := by
  simp only [dotProduct_eq_sum_mul, mulVec_apply_eq_sum_pluriharmonic_analysis, Pi.star_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH.apply i j]
  ring
private theorem quad_form_inv_mulVec_eq_inv_form {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (y : Fin r → ℂ) :
    star (G⁻¹ *ᵥ y) ⬝ᵥ G *ᵥ (G⁻¹ *ᵥ y) = star y ⬝ᵥ G⁻¹ *ᵥ y := by
  rw [Matrix.mulVec_mulVec, mul_inv_eq_one_of_posDef hG, Matrix.one_mulVec,
    star_mulVec_dotProduct_of_isHermitian (isHermitian_of_posDef (posDef_inv_of_posDef hG))]
private theorem star_smul_sub_dotProduct_mulVec_expand {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (P z : ℂ) (a c : Fin r → ℂ) :
    star (P • c - z • a) ⬝ᵥ G *ᵥ (P • c - z • a) =
      starRingEnd ℂ P * P * (star c ⬝ᵥ G *ᵥ c) - starRingEnd ℂ P * z * (star c ⬝ᵥ G *ᵥ a)
        - starRingEnd ℂ z * P * (star a ⬝ᵥ G *ᵥ c) + starRingEnd ℂ z * z * (star a ⬝ᵥ G *ᵥ a) := by
  simp only [starRingEnd_apply]
  simp only [star_sub, star_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, _root_.sub_dotProduct,
    _root_.dotProduct_sub, _root_.smul_dotProduct, _root_.dotProduct_smul, smul_eq_mul]
  ring
private theorem complex_norm_sq_eq_re_sq_add_im_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder
variable {X : Type*} [MeasurableSpace X]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (c y : Fin r → ℂ) :
    ‖star y ⬝ᵥ c‖ ^ 2 ≤ (star c ⬝ᵥ G *ᵥ c).re * (star y ⬝ᵥ G⁻¹ *ᵥ y).re := by
  by_cases hy : y = 0
  · subst hy; simp
  have hHi := isHermitian_of_posDef (posDef_inv_of_posDef hG)
  have hP := re_pos_and_im_eq_zero_of_pos (star_dotProduct_mulVec_pos_of_posDef (posDef_inv_of_posDef hG) hy)
  have f2 : star (G⁻¹ *ᵥ y) ⬝ᵥ G *ᵥ c = star y ⬝ᵥ c := by
    rw [star_mulVec_dotProduct_of_isHermitian hHi, Matrix.mulVec_mulVec, inv_mul_eq_one_of_posDef hG, Matrix.one_mulVec]
  have f3 : star c ⬝ᵥ G *ᵥ (G⁻¹ *ᵥ y) = starRingEnd ℂ (star y ⬝ᵥ c) := by
    rw [Matrix.mulVec_mulVec, mul_inv_eq_one_of_posDef hG, Matrix.one_mulVec, conj_star_dotProduct]
  have key := re_star_dotProduct_mulVec_nonneg_of_posDef hG ((star y ⬝ᵥ G⁻¹ *ᵥ y) • c - (star y ⬝ᵥ c) • (G⁻¹ *ᵥ y))
  rw [star_smul_sub_dotProduct_mulVec_expand, quad_form_inv_mulVec_eq_inv_form hG, f2, f3] at key
  obtain ⟨p, hp⟩ : ∃ p : ℝ, star y ⬝ᵥ G⁻¹ *ᵥ y = p :=
    ⟨(star y ⬝ᵥ G⁻¹ *ᵥ y).re, Complex.ext (by simp) (by simp [hP.2])⟩
  rw [hp] at key hP ⊢
  generalize star y ⬝ᵥ c = z at key ⊢
  generalize star c ⬝ᵥ G *ᵥ c = B at key ⊢
  simp only [Complex.conj_ofReal, Complex.ofReal_re] at key hP ⊢
  rw [complex_norm_sq_eq_re_sq_add_im_sq]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im] at key
  nlinarith [hP.1, key]
end ReciprocityTheory.GeometryOfNumbersTheory
