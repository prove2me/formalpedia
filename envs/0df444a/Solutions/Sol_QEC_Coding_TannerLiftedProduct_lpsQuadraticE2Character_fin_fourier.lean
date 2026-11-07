-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_fin_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:54:24.383214+00:00
-- url     : https://prove2.me/submissions/aa11c5e1-557f-44be-8417-9f094498f17e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticCharacter_fourier
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_ne_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    (∑ a : Fin q, lpsQuadraticE2Character q (a.val:ZMod q) *
      ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod q)) =
      lpsQuadraticE2Character q (n:ZMod q) *
        gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) := by
  have h := lpsQuadraticCharacter_fourier (ZMod q) (lpsQuadraticE2Character q)
    (lpsQuadraticE2Character_ne_one q hq2) ((quadraticChar_isQuadratic (ZMod q)).comp _)
    (ZMod.stdAddChar (N:=q)) (n:ZMod q)
  have hs := (ZMod.finEquiv q).sum_comp (fun a : ZMod q =>
    lpsQuadraticE2Character q a*ZMod.stdAddChar ((n:ZMod q)*a))
  rw [← hs] at h
  change (∑ a : Fin q, lpsQuadraticE2Character q (ZMod.finEquiv q a) *
    ZMod.stdAddChar ((n:ZMod q)*ZMod.finEquiv q a)) = _ at h
  simpa only [← lpsFin_cast_finEquiv,Int.cast_mul,Int.cast_natCast,mul_comm] using h
end QEC.Coding.TannerLiftedProduct
