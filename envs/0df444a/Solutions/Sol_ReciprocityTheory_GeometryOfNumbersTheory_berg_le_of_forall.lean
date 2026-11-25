-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.berg_le_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:17.887297+00:00
-- url     : https://prove2.me/submissions/33654996-47c3-4753-b2fb-a7166b438f87

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_bNormSq_eq_re
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_berg_eq_quad
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sum_mul_eq_star_dot
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
theorem _root_.solution (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (hpos : (bGram μ s w).PosDef) (x : X) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ c : Fin r → ℂ, ‖∑ i, c i * s i x‖ ^ 2 * w x ≤ M * bNormSq μ s w c) :
    bergmanDensity μ s w x ≤ M := by
  have hI : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ := by
    assumption
  have h := hM ((bGram μ s w)⁻¹ *ᵥ star fun i => s i x)
  rw [sum_mul_eq_star_dot s ((bGram μ s w)⁻¹ *ᵥ star fun i => s i x) x, bNormSq_eq_re μ s w hI,
    quad_form_inv_mulVec_eq_inv_form hpos] at h
  have hq := re_star_dotProduct_mulVec_nonneg_of_posDef (posDef_inv_of_posDef hpos) (star fun i => s i x)
  rw [berg_eq_quad]
  generalize star (star fun i => s i x) ⬝ᵥ (bGram μ s w)⁻¹ *ᵥ (star fun i => s i x) = q at h hq ⊢
  rw [complex_norm_sq_eq_re_sq_add_im_sq] at h
  have hwx := hw x
  rcases hq.eq_or_lt with h0 | hq0
  · rw [← h0]
    simpa using hM0
  · have h3 : q.re ^ 2 * w x ≤ M * q.re := by nlinarith [sq_nonneg q.im]
    nlinarith
end ReciprocityTheory.GeometryOfNumbersTheory
