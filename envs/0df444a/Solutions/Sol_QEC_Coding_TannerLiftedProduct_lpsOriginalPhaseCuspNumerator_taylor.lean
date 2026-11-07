-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspNumerator_taylor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:49:07.479194+00:00
-- url     : https://prove2.me/submissions/75e1ec76-6c53-44d3-9f9f-e1e79ccf8b6b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelRoot_inversePower_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedAffineCusp_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJZSeries_mapC
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_comp_const_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_comp_pow
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
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) (m : ℕ) (hm : m ≠ 0) (r : ℚ)
    (hr : ∃ z : ℤ, (N : ℚ) * r = z) :
    lpsOriginalPhaseCuspNumerator ℂ N m hm
      (Function.Periodic.qParam 1 (r : ℂ)) =
        lpsOriginalTaylorSeries (lpsOriginalClearedAffineCusp m m r) := by
  have hf : AnalyticAt ℂ (fun q : ℂ => lpsOriginalJQCoefficient
      (Function.Periodic.qParam 1 (r : ℂ)*q)) 0 :=
    lpsOriginalJQCoefficient_analytic_zero.fun_comp_of_eq (by fun_prop) (by simp)
  rw [lpsOriginalClearedAffineCusp_taylor m m hm r]
  simp only [Nat.sub_self,pow_zero,one_mul]
  rw [lpsOriginalTaylorSeries_comp_pow hf m hm,
    lpsOriginalTaylorSeries_comp_const_mul lpsOriginalJQCoefficient_analytic_zero,
    ← lpsOriginalJZSeries_mapC]
  rw [lpsOriginalPhaseCuspNumerator,
    lpsOriginalLevelRoot_inversePower_eq ℂ N hN _
      (lpsOriginalLevelNomePhase_pow N r hr)]
  rfl
end QEC.Coding.TannerLiftedProduct
