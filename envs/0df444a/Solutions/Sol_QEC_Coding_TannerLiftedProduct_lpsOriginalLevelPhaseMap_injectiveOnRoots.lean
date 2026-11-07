-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseMap_injectiveOnRoots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:39:11.956445+00:00
-- url     : https://prove2.me/submissions/2aaa872d-4fbb-4abb-896f-ce397081b0d1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelPrimitivePhase_isPrimitive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelPhasePolynomial_product
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
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) (K : Type*) [Field K]
    (φ : lpsOriginalLevelPhaseRing N →+* K) (hNK : (N : K) ≠ 0) :
    Set.InjOn φ {z : lpsOriginalLevelPhaseRing N | z^N = 1} := by
  let : NeZero N := ⟨hN.ne'⟩
  let ζ := lpsOriginalLevelPrimitivePhase N hN
  have he := congrArg (Polynomial.map φ) (lpsOriginalLevelPhasePolynomial_product N hN)
  simp only [Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,
    φ.map_one,Polynomial.map_prod,φ.map_pow] at he
  have hs : (∏ i ∈ Finset.range N,
      (Polynomial.X - Polynomial.C ((φ ζ)^i))).Separable := by
    rw [← he]
    exact Polynomial.separable_X_pow_sub_C (1 : K) hNK one_ne_zero
  intro a ha b hb hab
  obtain ⟨i,hi,hia⟩ := (lpsOriginalLevelPrimitivePhase_isPrimitive N hN).eq_pow_of_pow_eq_one ha
  obtain ⟨j,hj,hjb⟩ := (lpsOriginalLevelPrimitivePhase_isPrimitive N hN).eq_pow_of_pow_eq_one hb
  have hij : i = j := by
    apply hs.inj_of_prod_X_sub_C (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj)
    simpa only [ζ,← map_pow,hia,hjb] using hab
  exact hia.symm.trans ((congrArg (fun k => ζ^k) hij).trans hjb)
end QEC.Coding.TannerLiftedProduct
