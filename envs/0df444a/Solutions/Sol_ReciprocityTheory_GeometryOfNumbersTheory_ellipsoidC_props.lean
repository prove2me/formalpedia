-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.ellipsoidC_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:29:05.197681+00:00
-- url     : https://prove2.me/submissions/e2a11a72-cb73-41bf-af49-52ba062871d9

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
private theorem isBounded_preimage_sqBall_complex_of_det_ne_zero {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (hdet : B.det ≠ 0) (R : ℝ) :
    Bornology.IsBounded (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hS : IsCompact (sqBall r ℂ R) :=
    Metric.isCompact_of_isClosed_isBounded (sqBall_isClosed r R) (sqBall_isBounded r R)
  have hc' : Continuous ((Matrix.toLin' B⁻¹).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hS.image hc').isBounded.subset ?_
  intro y hy
  refine ⟨(Matrix.toLin' B).restrictScalars ℝ y, hy, ?_⟩
  show Matrix.mulVec B⁻¹ (Matrix.mulVec B y) = y
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]
private theorem convex_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    Convex ℝ (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) :=
  Convex.linear_preimage (sqBall_convex (E := ℂ) r R) ((Matrix.toLin' B).restrictScalars ℝ)
private theorem neg_mem_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    ∀ y ∈ ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R,
      -y ∈ ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R := by
  intro y hy
  rw [Set.mem_preimage, map_neg]
  exact sqBall_neg (E := ℂ) r R _ hy
private theorem measurableSet_preimage_sqBall_complex {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (R : ℝ) :
    MeasurableSet (((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' sqBall r ℂ R) := by
  have hc : Continuous ((Matrix.toLin' B).restrictScalars ℝ) :=
    LinearMap.continuous_of_finiteDimensional _
  exact ((sqBall_isClosed r R).preimage hc).measurableSet
private lemma hermitianEllipsoid_props_of_eq {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : G = Bᴴ * B) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  subst hB
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := hG.det_pos
    rw [detC_eq, h0] at h1
    simp at h1
  rw [setC_eq]
  exact ⟨convex_preimage_sqBall_complex B R, neg_mem_preimage_sqBall_complex B R, isBounded_preimage_sqBall_complex_of_det_ne_zero B hdet R, measurableSet_preimage_sqBall_complex B R⟩
end ReciprocityTheory.GeometryOfNumbersTheory
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.PosDef) (R : ℝ) :
    Convex ℝ {y | qC G y ≤ R ^ 2} ∧ (∀ y ∈ {y | qC G y ≤ R ^ 2}, -y ∈ {y | qC G y ≤ R ^ 2}) ∧
      Bornology.IsBounded {y | qC G y ≤ R ^ 2} ∧ MeasurableSet {y | qC G y ≤ R ^ 2} := by
  obtain ⟨B, hB⟩ := exists_factor_C hG
  exact hermitianEllipsoid_props_of_eq hG B hB R
end ReciprocityTheory.GeometryOfNumbersTheory
