-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2_real_shift_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:54:23.217198+00:00
-- url     : https://prove2.me/submissions/85063a33-e4f3-4977-96fe-9a13a070aa0e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_real_shift
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (a : ℤ) (z : ℍ) :
    HasSum (fun n : ℕ =>
      (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n : ℂ) *
        ZMod.stdAddChar (((a*(n:ℤ)):ℤ):ZMod N) *
        Function.Periodic.qParam 1 (z:ℂ)^n)
      (EisensteinSeries.E2 (((a:ℝ)/(N:ℝ)) +ᵥ z)) := by
  have h : HasSum (fun n : ℕ =>
      (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n : ℂ) *
        Function.Periodic.qParam 1 ((((a:ℝ)/(N:ℝ)) +ᵥ z:ℍ):ℂ)^n)
      (EisensteinSeries.E2 (((a:ℝ)/(N:ℝ)) +ᵥ z)) := by
    simpa only [Function.Periodic.qParam,Complex.ofReal_one,div_one,smul_eq_mul] using
      EisensteinSeries.hasSum_qExpansion_E2 (z:=((a:ℝ)/(N:ℝ)) +ᵥ z)
  convert h using 1
  ext n
  rw [lpsQParam_real_shift,mul_pow]
  have hc := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=N)) n (a:ZMod N)
  simp only [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast] at hc ⊢
  rw [← hc]
  ring
end QEC.Coding.TannerLiftedProduct
