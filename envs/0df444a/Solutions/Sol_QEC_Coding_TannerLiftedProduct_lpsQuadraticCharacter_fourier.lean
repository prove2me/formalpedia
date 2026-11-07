-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticCharacter_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:18.391002+00:00
-- url     : https://prove2.me/submissions/d1480ae8-9f22-450f-a3a2-98f5bded314b

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
theorem _root_.solution (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ≠1) (hχq : χ.IsQuadratic) (ψ : AddChar F ℂ) (a : F) :
    (∑ r : F, χ r*ψ (a*r))=χ a*gaussSum χ ψ := by
  classical
  by_cases ha : a=0
  · subst a
    simp only [zero_mul,AddChar.map_zero_eq_one,mul_one,MulChar.map_zero,zero_mul]
    have h := gaussSum_one_right hχ
    simpa only [gaussSum,AddChar.one_apply,mul_one] using h
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    have h := gaussSum_mulShift_eq χ ψ hu.unit
    rw [hχq.inv] at h
    simpa only [gaussSum,AddChar.mulShift_apply,hu.unit_spec] using h
end QEC.Coding.TannerLiftedProduct
