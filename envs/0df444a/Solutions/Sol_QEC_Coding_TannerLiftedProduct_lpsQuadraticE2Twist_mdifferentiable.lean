-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_mdifferentiable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:54:35.567223+00:00
-- url     : https://prove2.me/submissions/5fcaf086-f2e7-4f40-8a5e-85f179098e79

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_real_shift_mdifferentiable
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
theorem _root_.solution (q : ℕ) [Fact q.Prime] :
    MDiff (fun z : ℍ => lpsQuadraticE2Twist q z) := by
  classical
  unfold lpsQuadraticE2Twist
  have h : MDiff (∑ a : Fin q, lpsQuadraticE2Character q (a.val:ZMod q) •
    (fun z : ℍ => EisensteinSeries.E2 (((a.val:ℝ)/(q:ℝ)) +ᵥ z))) :=
    MDifferentiable.sum (fun (a : Fin q) ha =>
      MDifferentiable.const_smul _ (lpsE2_real_shift_mdifferentiable ((a.val:ℝ)/(q:ℝ))))
  have h2 := MDifferentiable.const_smul
    (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ h
  convert h2 using 1
  ext z
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
end QEC.Coding.TannerLiftedProduct
