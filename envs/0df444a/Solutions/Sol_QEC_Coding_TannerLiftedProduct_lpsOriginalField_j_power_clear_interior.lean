-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalField_j_power_clear_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:25:24.918477+00:00
-- url     : https://prove2.me/submissions/9c6341da-b293-41d7-af85-9a672b392392

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_interior_order_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_sub_constant_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_sub_constant_order_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_clear_power
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalJPowerClearingDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalJPowerClearingDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalJPowerClearingDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalJPowerClearingDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f : K)
    (hno : ∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) ≠ 0 →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f) :
    ∃ k : ℕ, ∀ x : Q, 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x)
      ((algebraMap P K Polynomial.X)^k*f) := by
  classical
  let bad := lpsOriginalField_negativeInteriorOrders_finite N hpos hN f
  let B := bad.toFinset
  let j : K := algebraMap P K Polynomial.X
  have hj0 : j ≠ 0 := by
    simpa only [map_zero, sub_zero] using
      lpsOriginalFieldJ_sub_constant_ne_zero N hpos (0 : ℂ)
  have hposj (x : Q) (hx : x ∈ B) :
      0 < lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) j := by
    have hp : lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f < 0 :=
      (Set.Finite.mem_toFinset bad).mp hx
    have hz : lpsOriginalFilledJ N (Sum.inl x) = 0 := by
      by_contra hn
      exact (not_le_of_gt hp) (hno x hn)
    simpa only [map_zero, sub_zero] using
      lpsOriginalFieldJ_sub_constant_order_pos N hpos hN (0 : ℂ) x hz
  have hc : ∀ x : {x // x ∈ B}, ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x.val) (j^m*f) :=
    fun x => lpsOriginalFieldLocalOrder_clear_power N hpos hN
      (Sum.inl x.val) j f (hposj x.val x.property) hj0
  choose n hn using hc
  let k := B.attach.sup n
  refine ⟨k, fun x => ?_⟩
  by_cases hx : x ∈ B
  · exact hn ⟨x,hx⟩ k (Finset.le_sup (Finset.mem_attach B ⟨x,hx⟩))
  · have hf : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f := by
      apply le_of_not_gt
      intro hbad
      exact hx ((Set.Finite.mem_toFinset bad).mpr hbad)
    rw [AddValuation.map_mul, AddValuation.map_pow]
    exact add_nonneg (nsmul_nonneg
      (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x) k) hf
end QEC.Coding.TannerLiftedProduct
