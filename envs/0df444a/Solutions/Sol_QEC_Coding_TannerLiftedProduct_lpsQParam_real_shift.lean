-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQParam_real_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:19.511415+00:00
-- url     : https://prove2.me/submissions/32fa2522-11b5-4b61-a424-73ce8b6cd041

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
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
    Function.Periodic.qParam 1 (((a:ℝ)/(N:ℝ)) +ᵥ z : ℍ) =
      ZMod.stdAddChar (a:ZMod N)*Function.Periodic.qParam 1 (z:ℂ) := by
  rw [ZMod.stdAddChar_coe]
  simp only [Function.Periodic.qParam,UpperHalfPlane.coe_vadd,Complex.ofReal_div,
    Complex.ofReal_intCast,Complex.ofReal_natCast,Complex.ofReal_one,div_one]
  rw [show (2:ℂ)*Real.pi*Complex.I*((a:ℂ)/(N:ℂ)+(z:ℂ)) =
    (2:ℂ)*Real.pi*Complex.I*(a:ℂ)/(N:ℂ)+(2:ℂ)*Real.pi*Complex.I*(z:ℂ) by ring,
    Complex.exp_add]
end QEC.Coding.TannerLiftedProduct
