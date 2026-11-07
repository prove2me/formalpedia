-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:55:31.376317+00:00
-- url     : https://prove2.me/submissions/30e0e758-c6d6-41c1-bbe4-fa029b365bf7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_real_shift_hasSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Gauss_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_fin_fourier
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
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (z : ℍ) :
    HasSum (fun n : ℕ => -24*(ArithmeticFunction.sigma 1 n:ℂ) *
      lpsQuadraticE2Character q (n:ZMod q) * Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsQuadraticE2Twist q z) := by
  classical
  have hsum := hasSum_sum (s:=Finset.univ) (fun (a : Fin q) ha =>
    (lpsE2_real_shift_hasSum q (a.val:ℤ) z).mul_left
      (lpsQuadraticE2Character q (a.val:ZMod q)))
  have h := hsum.mul_left (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹
  change HasSum _ (lpsQuadraticE2Twist q z) at h
  convert h using 1
  ext n
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [show (∑ a : Fin q, lpsQuadraticE2Character q (a.val:ZMod q) *
    (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n:ℂ) *
    ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod q)) =
    (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n:ℂ) *
    (∑ a : Fin q, lpsQuadraticE2Character q (a.val:ZMod q)*
      ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod q)) by
        rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro a ha;ring]
  rw [lpsQuadraticE2Character_fin_fourier q hq2]
  by_cases hn : n=0
  · subst n
    simp [MulChar.map_zero]
  · simp only [if_neg hn]
    have hg := lpsQuadraticE2Gauss_ne_zero q hq2
    field_simp [hg]
end QEC.Coding.TannerLiftedProduct
