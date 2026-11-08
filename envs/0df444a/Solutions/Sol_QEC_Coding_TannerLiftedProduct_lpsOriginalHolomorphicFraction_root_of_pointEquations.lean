-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicFraction_root_of_pointEquations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:30:47.323729+00:00
-- url     : https://prove2.me/submissions/7d546491-9188-4d42-b619-dedcae58789f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Mathlib.Algebra.Polynomial.Homogenize
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : Polynomial LPSOriginalHolomorphicRing) (r : ℕ) (hp : p.natDegree ≤ r)
    (A B : LPSOriginalHolomorphicRing) (hB : B ≠ 0)
    (hpoint : ∀ τ : ℍ, B.val τ ≠ 0 →
      p.eval₂ (lpsOriginalHolomorphicPointEvaluation τ)
        (A.val τ / B.val τ) = 0) :
    p.eval₂ (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
      ((algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField A) /
        (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField B)) = 0 := by
  classical
  let H := MvPolynomial.eval ![A, B] (p.homogenize r)
  have hHpoint (τ : ℍ) (hb : B.val τ ≠ 0) : H.val τ = 0 := by
    let e := lpsOriginalHolomorphicPointEvaluation τ
    have he : e H = MvPolynomial.eval ![e A, e B] ((p.map e).homogenize r) := by
      dsimp only [H]
      rw [MvPolynomial.map_eval, ← Polynomial.homogenize_map]
      have hv : (e ∘ ![A, B]) = ![e A, e B] := by
        funext i
        fin_cases i <;> rfl
      rw [hv]
    rw [Polynomial.eval_homogenize ((Polynomial.natDegree_map_le).trans hp)
      ![e A, e B] hb, Polynomial.eval_map] at he
    change H.val τ = p.eval₂ (lpsOriginalHolomorphicPointEvaluation τ)
      (A.val τ / B.val τ) * B.val τ^r at he
    rw [hpoint τ hb, zero_mul] at he
    exact he
  have hmul : H * B = 0 := by
    apply Subtype.ext
    funext τ
    change H.val τ * B.val τ = 0
    by_cases hb : B.val τ = 0
    · rw [hb, mul_zero]
    · rw [hHpoint τ hb, zero_mul]
  have hH : H = 0 := (mul_eq_zero.mp hmul).resolve_right hB
  let e := algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
  have hb : e B ≠ 0 := fun hz => hB
    ((IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
      (hz.trans (map_zero e).symm))
  have he : e H = MvPolynomial.eval ![e A, e B] ((p.map e).homogenize r) := by
    dsimp only [H]
    rw [MvPolynomial.map_eval, ← Polynomial.homogenize_map]
    have hv : (e ∘ ![A, B]) = ![e A, e B] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
  rw [hH, map_zero, Polynomial.eval_homogenize
    ((Polynomial.natDegree_map_le).trans hp) ![e A, e B] hb,
    Polynomial.eval_map] at he
  exact (mul_eq_zero.mp he.symm).resolve_right (pow_ne_zero r hb)
end QEC.Coding.TannerLiftedProduct
