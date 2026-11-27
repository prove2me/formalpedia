-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.le_volume_ellipsoidC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:28:38.505808+00:00
-- url     : https://prove2.me/submissions/bcb6de21-2918-4d52-9224-22cc3612d5b2

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
private lemma exists_factor_C {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, G = Bᴴ * B := by
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
private lemma qC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) :
    qC (Bᴴ * B) y = ∑ k, ‖(B *ᵥ y) k‖ ^ 2 := by
  have h1 : (∑ i, ∑ j, starRingEnd ℂ (y i) * (Bᴴ * B) i j * y j) =
      dotProduct (star y) ((Bᴴ * B) *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply, RCLike.star_def]
  unfold qC
  rw [h1, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.re_sum, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  refine Finset.sum_congr rfl (fun k _ => by ring)
private lemma setC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    {y | qC (Bᴴ * B) y ≤ R ^ 2} = ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, qC_eq, LinearMap.restrictScalars_apply,
    Matrix.toLin'_apply, sqBall]
private lemma detC_eq {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) :
    (Bᴴ * B).det = (Complex.normSq B.det : ℂ) := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.normSq_eq_conj_mul_self]
  rfl
end ReciprocityTheory.GeometryOfNumbersTheory
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) {R : ℝ}
    (hR : 0 < R) :
    (2 * R ^ 2 / r) ^ r / G.det.re ≤ (volume {y : Fin r → ℂ | qC G y ≤ R ^ 2}).toReal := by
  obtain ⟨B, rfl⟩ := exists_factor_C hG
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [detC_eq, h0] at h1
    simp at h1
  have hN : 0 < Complex.normSq B.det := Complex.normSq_pos.2 hdet
  have hT : LinearMap.det ((Matrix.toLin' B).restrictScalars ℝ) = Complex.normSq B.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin']
    first
    | exact Algebra.norm_complex_apply _
    | simp [Algebra.norm_complex_apply]
  have hfin : volume (sqBall r ℂ R) ≠ ⊤ := (sqBall_isBounded (E := ℂ) r R).measure_lt_top.ne
  have hρ : 0 ≤ R / Real.sqrt r := div_nonneg hR.le (Real.sqrt_nonneg _)
  have hdisc : (volume (Metric.closedBall (0 : ℂ) (R / Real.sqrt r))).toReal
      = Real.pi * (R / Real.sqrt r) ^ 2 := by
    first
    | (simp only [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hρ, ENNReal.coe_toReal, NNReal.coe_real_pi] <;> ring_nf <;> done)
    | (simp [Complex.volume_closedBall, ENNReal.toReal_ofReal hρ] <;> ring_nf <;> done)
    | (simp [Complex.volume_closedBall, ENNReal.toReal_ofReal hρ, mul_comm] <;> done)
  have hbox : (2 * R ^ 2 / r) ^ r ≤ (volume (sqBall r ℂ R)).toReal := by
    have hmono := MeasureTheory.measure_mono (μ := volume) (box_subset_sqBall (E := ℂ) r (R := R))
    rw [MeasureTheory.volume_pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hmono
    have h2 := ENNReal.toReal_mono hfin hmono
    rw [ENNReal.toReal_pow, hdisc] at h2
    refine le_trans ?_ h2
    have hq : (R / Real.sqrt r) ^ 2 = R ^ 2 / r := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg r)]
    rw [hq]
    have hR2 : 0 ≤ R ^ 2 / (r : ℝ) := div_nonneg (sq_nonneg R) (Nat.cast_nonneg r)
    have hle : 2 * R ^ 2 / (r : ℝ) ≤ Real.pi * (R ^ 2 / r) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) hR2
    exact pow_le_pow_left₀ (by rw [mul_div_assoc]; exact mul_nonneg zero_le_two hR2) hle r
  rw [setC_eq, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rw [hT]; exact hN.ne'), hT,
    detC_eq, Complex.ofReal_re, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_inv, abs_of_pos hN, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hbox (inv_nonneg.2 hN.le)
end ReciprocityTheory.GeometryOfNumbersTheory
