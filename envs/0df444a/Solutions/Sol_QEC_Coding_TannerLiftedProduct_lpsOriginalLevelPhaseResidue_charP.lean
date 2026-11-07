-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseResidue_charP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:37:06.74207+00:00
-- url     : https://prove2.me/submissions/b0894abd-6f2a-4719-a248-61de1040f330

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelPhasePrime_comap
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
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    CharP (LPSOriginalLevelPhaseResidue N hN p hp) p := by
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨fun n => ?_⟩
  change (Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp)
    (algebraMap ℤ (lpsOriginalLevelPhaseRing N) (n : ℤ)) = 0) ↔ p ∣ n
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change (n : ℤ) ∈ (lpsOriginalLevelPhasePrime N hN p hp).comap
    (algebraMap ℤ (lpsOriginalLevelPhaseRing N)) ↔ p ∣ n
  rw [lpsOriginalLevelPhasePrime_comap]
  change ((n : ℤ) : ZMod p) = 0 ↔ p ∣ n
  simpa only [Int.cast_natCast] using (CharP.cast_eq_zero_iff (ZMod p) p n)
end QEC.Coding.TannerLiftedProduct
