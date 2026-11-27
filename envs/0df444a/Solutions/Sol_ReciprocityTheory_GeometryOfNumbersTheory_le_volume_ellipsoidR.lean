-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.le_volume_ellipsoidR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:28:43.378279+00:00
-- url     : https://prove2.me/submissions/839f37e4-5a6d-441a-852e-a6044d130348

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_box_subset_sqBall
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_sqBall_isBounded

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
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
private lemma exists_factor_R {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin r) (Fin r) ℝ, G = Bᵀ * B := by
  have hC : ∃ B : Matrix (Fin r) (Fin r) ℝ, G = Bᴴ * B := by
    first
    | exact Matrix.posSemidef_iff_eq_transpose_mul_self.1 hG.posSemidef
    | exact (Matrix.posSemidef_iff_eq_conjTranspose_mul_self).1 hG.posSemidef
    | exact hG.posSemidef.exists_eq_conjTranspose_mul_self
    | (refine ⟨hG.posSemidef.sqrt, ?_⟩
       rw [hG.posSemidef.posSemidef_sqrt.isHermitian.eq, hG.posSemidef.sqrt_mul_self])
    | (refine ⟨CFC.sqrt G, ?_⟩
       have h0 : 0 ≤ G := hG.posSemidef.nonneg
       have hs : (CFC.sqrt G)ᴴ = CFC.sqrt G := (CFC.sqrt_nonneg G).isSelfAdjoint.star_eq
       rw [hs, CFC.sqrt_mul_sqrt_self G h0])
  obtain ⟨B, hB⟩ := hC
  exact ⟨B, by rw [hB, Matrix.conjTranspose_eq_transpose_of_trivial]⟩
private lemma qR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) :
    qR (Bᵀ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : qR (Bᵀ * B) y = dotProduct y ((Bᵀ * B) *ᵥ y) := by
    simp only [qR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, Real.norm_eq_abs, sq_abs, sq, abs_mul_abs_self]
private lemma setR_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    {y | qR (Bᵀ * B) y ≤ R ^ 2} = (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qR_eq, Matrix.toLin'_apply, sqBall]
  skip
end ReciprocityTheory.GeometryOfNumbersTheory
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) {R : ℝ}
    (hR : 0 < R) :
    (2 * R / Real.sqrt r) ^ r / Real.sqrt G.det ≤
      (volume {y : Fin r → ℝ | qR G y ≤ R ^ 2}).toReal := by
  obtain ⟨B, rfl⟩ := exists_factor_R hG
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at h1
    exact lt_irrefl _ h1
  have hsq : Real.sqrt (Bᵀ * B).det = |B.det| := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]
  have habs : 0 < |B.det| := abs_pos.2 hdet
  have hfin : volume (sqBall r ℝ R) ≠ ⊤ := (sqBall_isBounded (E := ℝ) r R).measure_lt_top.ne
  have hbox : (2 * R / Real.sqrt r) ^ r ≤ (volume (sqBall r ℝ R)).toReal := by
    have hmono := MeasureTheory.measure_mono (μ := volume) (box_subset_sqBall (E := ℝ) r (R := R))
    rw [MeasureTheory.volume_pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Real.volume_closedBall] at hmono
    have h2 := ENNReal.toReal_mono hfin hmono
    rw [ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (mul_nonneg zero_le_two (div_nonneg hR.le (Real.sqrt_nonneg _)))] at h2
    rw [mul_div_assoc]
    exact h2
  rw [setR_eq, MeasureTheory.Measure.addHaar_preimage_linearMap _
      (by rw [LinearMap.det_toLin']; exact hdet), LinearMap.det_toLin', hsq,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hbox (inv_nonneg.2 habs.le)
end ReciprocityTheory.GeometryOfNumbersTheory
