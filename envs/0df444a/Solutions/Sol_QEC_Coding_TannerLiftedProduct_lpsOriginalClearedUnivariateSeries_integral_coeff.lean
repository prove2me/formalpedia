-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateSeries_integral_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:33:02.202691+00:00
-- url     : https://prove2.me/submissions/0e3238be-9b10-4bda-9bbf-38acda5b68b4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegralSeries_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedUnivariateTerm_coeff
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
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N D : ℕ) (hN : 0<N) (K : PowerSeries ℂ) (p : Polynomial ℂ)
    (hd : p.natDegree≤D) (hK0 : K.constantCoeff=1)
    (hK : ∀ n, IsIntegral ℤ (K.coeff n))
    (hc : ∀ n, IsIntegral ℤ
      ((lpsOriginalClearedUnivariateSeries N D K p).coeff n)) :
    ∀ n, IsIntegral ℤ (p.coeff n) := by
  classical
  have hind : ∀ k : ℕ, ∀ n : ℕ, n≤D → D-n=k → IsIntegral ℤ (p.coeff n) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hn hk
      let S := (Finset.range (D+1)).erase n
      let t := N*(D-n)
      let f := fun i : ℕ =>
        (PowerSeries.C (p.coeff i)*PowerSeries.X^(N*(D-i))*K^i).coeff t
      have hf : ∀ i∈S, IsIntegral ℤ (f i) := by
        intro i hi
        have hiD : i≤D := by
          have := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
          omega
        have hin : i≠n := (Finset.mem_erase.mp hi).1
        dsimp only [f]
        rw [lpsOriginalClearedUnivariateTerm_coeff]
        by_cases hit : i<n
        · have he : ¬N*(D-i)≤t := by
            dsimp only [t]
            exact not_le_of_gt (Nat.mul_lt_mul_of_pos_left (by omega : D-n<D-i) hN)
          rw [if_neg he,mul_zero]
          exact isIntegral_zero
        · have hni : n < i := by omega
          have hp := ih (D-i) (by omega) i hiD rfl
          split_ifs
          · exact hp.mul (lpsOriginalIntegralSeries_pow K hK i _)
          · simpa only [mul_zero] using (isIntegral_zero : IsIntegral ℤ (0:ℂ))
      have hsum : IsIntegral ℤ (∑ i∈S, f i) := IsIntegral.sum f hf
      have hfn : f n=p.coeff n := by
        dsimp only [f,t]
        rw [lpsOriginalClearedUnivariateTerm_coeff,if_pos le_rfl,Nat.sub_self,
          PowerSeries.coeff_zero_eq_constantCoeff_apply,map_pow,hK0,one_pow,mul_one]
      have he : (lpsOriginalClearedUnivariateSeries N D K p).coeff t =
          (∑ i∈S, f i)+p.coeff n := by
        rw [lpsOriginalClearedUnivariateSeries,map_sum]
        exact (Finset.sum_erase_add _ _ (Finset.mem_range.mpr (by omega))).symm.trans
          (congrArg ((∑ i∈S, f i)+ ·) hfn)
      have h := (hc t).sub hsum
      rw [he,add_sub_cancel_left] at h
      exact h
  intro n
  by_cases hn : n≤D
  · exact hind (D-n) n hn rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree<n)]
    exact isIntegral_zero
end QEC.Coding.TannerLiftedProduct
