-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.ellipsoidR_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:29:09.170412+00:00
-- url     : https://prove2.me/submissions/ad9decfa-559e-4484-9b93-2c76e4c1fe7f

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_sqBall_convex
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_sqBall_isBounded
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_sqBall_isClosed
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_sqBall_neg

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
private theorem isBounded_preimage_sqBall_real_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hS : IsCompact (sqBall r ℝ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous (Matrix.toLin' B⁻¹) := LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨Matrix.toLin' B y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]
private theorem convex_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    Convex ℝ ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) :=
  Convex.linear_preimage (sqBall_convex (E := ℝ) r R) (Matrix.toLin' B)
private theorem neg_mem_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    ∀ y ∈ (Matrix.toLin' B) ⁻¹' sqBall r ℝ R, -y ∈ (Matrix.toLin' B) ⁻¹' sqBall r ℝ R := by
  intro y hy
  rw [Set.mem_preimage, map_neg]
  exact sqBall_neg (E := ℝ) r R _ hy
private theorem measurableSet_preimage_sqBall_real {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (R : ℝ) :
    MeasurableSet ((Matrix.toLin' B) ⁻¹' sqBall r ℝ R) := by
  have hc : Continuous (Matrix.toLin' B) := LinearMap.continuous_of_finiteDimensional _
  exact ((sqBall_isClosed r R).preimage hc).measurableSet
private lemma realEllipsoid_props_of_eq {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (B : Matrix (Fin r) (Fin r) ℝ)
    (hB : G = Bᵀ * B) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  subst hB
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at h1
    exact lt_irrefl _ h1
  rw [setR_eq]
  exact ⟨convex_preimage_sqBall_real B R, neg_mem_preimage_sqBall_real B R, isBounded_preimage_sqBall_real_of_det_ne_zero B hdet R, measurableSet_preimage_sqBall_real B R⟩
end ReciprocityTheory.GeometryOfNumbersTheory
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qR G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qR G y ≤ R ^ 2}, -y ∈ {y | qR G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qR G y ≤ R ^ 2} ∧ MeasurableSet {y | qR G y ≤ R ^ 2} := by
  obtain ⟨B, hB⟩ := exists_factor_R hG
  exact realEllipsoid_props_of_eq hG B hB R
end ReciprocityTheory.GeometryOfNumbersTheory
