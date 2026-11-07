-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.heightOne_primeUnder_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:32:39.970284+00:00
-- url     : https://prove2.me/submissions/ac8ddcaf-1eab-41b6-92c5-aa118dc2fac3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
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
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.HasGoingDown R S]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥)
    (q : Ideal S) [q.IsPrime] (hq : q.height = 1) (hle : P ≤ q.under R) :
    q.under R = P := by
  by_contra hn
  have hlt : P < q.under R := lt_of_le_of_ne hle (Ne.symm hn)
  obtain ⟨Q,hQlt,hQprime,hQover⟩ := Ideal.exists_ideal_lt_liesOver_of_lt
    (p := P) (q := q.under R) q hlt
  let : Q.IsPrime := hQprime
  let : Q.LiesOver P := hQover
  have hbot : (⊥ : Ideal S).under R = ⊥ := by
    change RingHom.ker (algebraMap R S) = ⊥
    exact (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)
  have hQne : Q ≠ ⊥ := by
    intro hz
    apply hP
    rw [Q.over_def P,hz,hbot]
  have hQheight : 1 ≤ Q.height :=
    Order.one_le_iff_ne_zero.mpr (Q.height_eq_zero_iff_eq_bot.not.mpr hQne)
  have htwo : (2 : ℕ∞) ≤ 1 := calc
    (2 : ℕ∞) = 1 + 1 := rfl
    _ ≤ Q.height + 1 := by simpa only [add_comm] using add_le_add_right hQheight (1 : ℕ∞)
    _ ≤ q.height := Ideal.height_add_one_le_of_lt_of_isPrime hQlt
    _ = 1 := hq
  norm_num at htwo
end QEC.Coding.AlgebraicGeometry
