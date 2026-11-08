-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalField_reciprocal_polynomial_clear_away
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:13:13.926581+00:00
-- url     : https://prove2.me/submissions/0bb1590f-aba2-4a1d-b281-1a860752bc4c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityFiniteFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPoleClearingAway
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalPolynomialMap_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_clear_power
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_negativeInfinityOrders_finite
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_reciprocal_integral_iff_regularPoints
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityEvaluation_polynomial
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
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityPoleClearingAwayDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f : K) (α : ℂ)
    (hα : ∀ x : S, lpsOriginalInfinityCoordinate N hpos hN x = α →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos x.val f) :
    ∃ H : P, H.eval α ≠ 0 ∧
      (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem
        (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos H*f) := by
  classical
  let φ := lpsOriginalReciprocalComplexFieldPolynomialMap N hpos
  let β := lpsOriginalInfinityCoordinate N hpos hN
  let bad := lpsOriginalField_negativeInfinityOrders_finite N hpos hN f
  let B := bad.toFinset
  let D : S → P := fun y => Polynomial.X - Polynomial.C (β y)
  let A : P := ∏ y ∈ B, D y
  have hAnz : A ≠ 0 := (Polynomial.monic_prod_X_sub_C β B).ne_zero
  have hi := lpsOriginalReciprocalPolynomialMap_injective N hpos
  have hAnzk : φ A ≠ 0 := fun hz => hAnz (hi (hz.trans (map_zero _).symm))
  have hnon (x : S) (p : P) : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x.val (φ p) :=
    lpsOriginalReciprocalFieldPolynomialMap_order_nonnegative N hpos hN x.val x.property p
  have hposA (y : S) (hy : y ∈ B) :
      0 < lpsOriginalFieldLocalOrder N hN hpos y.val (φ A) := by
    let Rest : P := ∏ x ∈ B.erase y, D x
    have hsplit : A = Rest * D y := (Finset.prod_erase_mul B D hy).symm
    have hp : 0 < lpsOriginalFieldLocalOrder N hN hpos y.val (φ (D y)) := by
      apply (lpsOriginalInfinityEvaluation_eq_zero_iff_order_pos N hpos hN
        y.val y.property (lpsOriginalInfinityPolynomialChartMap N hpos (D y))).mp
      rw [lpsOriginalInfinityEvaluation_polynomial]
      simp only [D,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sub_self,β]
    rw [hsplit,map_mul,AddValuation.map_mul]
    exact lt_of_lt_of_le hp (le_add_of_nonneg_left (hnon y Rest))
  have hc : ∀ y : {y // y ∈ B}, ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos y.val.val ((φ A)^m*f) :=
    fun y => lpsOriginalFieldLocalOrder_clear_power N hpos hN y.val.val
      (φ A) f (hposA y.val y.property) hAnzk
  choose n hn using hc
  let m := B.attach.sup n
  have hAα : A.eval α ≠ 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    simp only [D,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
    intro hz
    have hbad : lpsOriginalFieldLocalOrder N hN hpos y.val f < 0 :=
      (Set.Finite.mem_toFinset bad).mp hy
    exact (not_le_of_gt hbad) (hα y (sub_eq_zero.mp hz).symm)
  refine ⟨A^m,by simpa only [Polynomial.eval_pow] using pow_ne_zero m hAα,?_⟩
  apply (lpsOriginalField_reciprocal_integral_iff_regularPoints N hpos hN _).mpr
  intro x
  rw [map_pow]
  by_cases hx : x ∈ B
  · exact hn ⟨x,hx⟩ m (Finset.le_sup (Finset.mem_attach B ⟨x,hx⟩))
  · have hf : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x.val f := by
      apply le_of_not_gt
      intro hbad
      exact hx ((Set.Finite.mem_toFinset bad).mpr hbad)
    rw [AddValuation.map_mul,AddValuation.map_pow]
    exact add_nonneg (nsmul_nonneg (hnon x A) m) hf
end QEC.Coding.TannerLiftedProduct
