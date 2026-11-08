-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalField_polynomial_clear_away
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:33:17.322597+00:00
-- url     : https://prove2.me/submissions/a47c7c6c-983c-47aa-be2e-05c8b7b31456

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPoleClearingAway
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_interior_order_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_sub_constant_order_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_clear_power
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_polynomial_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_integral_iff_noInteriorPole
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_negativeInteriorOrders_finite
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
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalPoleAwayDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalPoleAwayDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalPoleAwayDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalPoleAwayDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f : K) (α : ℂ)
    (hα : ∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) = α →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f) :
    ∃ H : P, H.eval α ≠ 0 ∧ IsIntegral P (algebraMap P K H*f) := by
  classical
  let bad := lpsOriginalField_negativeInteriorOrders_finite N hpos hN f
  let B := bad.toFinset
  let D : Q → P := fun y => Polynomial.X - Polynomial.C (lpsOriginalFilledJ N (Sum.inl y))
  let A : P := ∏ y ∈ B, D y
  have hAnz : A ≠ 0 := (Polynomial.monic_prod_X_sub_C
    (fun y => lpsOriginalFilledJ N (Sum.inl y)) B).ne_zero
  have hi : Function.Injective (algebraMap P K) :=
    (algebraMap J K).injective.comp (IsFractionRing.injective P J)
  have hAnzk : algebraMap P K A ≠ 0 := fun hz => hAnz (hi (hz.trans (map_zero _).symm))
  have hnon (x : Q) (p : P) : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) (algebraMap P K p) :=
    lpsOriginalFieldLocalOrder_polynomial_nonnegative N hN hpos (Sum.inl x)
      (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x) p
  have hposA (y : Q) (hy : y ∈ B) :
      0 < lpsOriginalFieldLocalOrder N hN hpos (Sum.inl y) (algebraMap P K A) := by
    let Rest : P := ∏ x ∈ B.erase y, D x
    have hsplit : A = Rest * D y := (Finset.prod_erase_mul B D hy).symm
    have hp : 0 < lpsOriginalFieldLocalOrder N hN hpos (Sum.inl y) (algebraMap P K (D y)) := by
      rw [show algebraMap P K (D y) = algebraMap P K Polynomial.X -
        algebraMap ℂ K (lpsOriginalFilledJ N (Sum.inl y)) by dsimp only [D];rw [map_sub];rfl]
      exact lpsOriginalFieldJ_sub_constant_order_pos N hpos hN _ y rfl
    rw [hsplit,map_mul,AddValuation.map_mul]
    exact lt_of_lt_of_le hp (le_add_of_nonneg_left (hnon y Rest))
  have hc : ∀ y : {y // y ∈ B}, ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl y.val) ((algebraMap P K A)^m*f) :=
    fun y => lpsOriginalFieldLocalOrder_clear_power N hpos hN (Sum.inl y.val)
      (algebraMap P K A) f (hposA y.val y.property) hAnzk
  choose n hn using hc
  let m := B.attach.sup n
  have hAα : A.eval α ≠ 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    simp only [D,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
    intro hz
    have hbad : lpsOriginalFieldLocalOrder N hN hpos (Sum.inl y) f < 0 :=
      (Set.Finite.mem_toFinset bad).mp hy
    exact (not_le_of_gt hbad) (hα y (sub_eq_zero.mp hz).symm)
  refine ⟨A^m,by simpa only [Polynomial.eval_pow] using pow_ne_zero m hAα,?_⟩
  apply (lpsOriginalField_integral_iff_noInteriorPole N hpos hN _).mpr
  intro x
  rw [map_pow]
  by_cases hx : x ∈ B
  · exact hn ⟨x,hx⟩ m (Finset.le_sup (Finset.mem_attach B ⟨x,hx⟩))
  · have hf : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f := by
      apply le_of_not_gt
      intro hbad
      exact hx ((Set.Finite.mem_toFinset bad).mpr hbad)
    rw [AddValuation.map_mul,AddValuation.map_pow]
    exact add_nonneg (nsmul_nonneg (hnon x A) m) hf
end QEC.Coding.TannerLiftedProduct
