-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFunction_periodic_comp_ofComplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:50:33.9001+00:00
-- url     : https://prove2.me/submissions/4de28961-92ea-47d1-ac98-3999eef37d0a

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
theorem _root_.solution (f : ℍ→ℂ)
    (hf : ∀ z, f ((1:ℝ) +ᵥ z)=f z) : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1 := by
  intro z
  by_cases hz : 0<z.im
  · have hz1 : 0<(z+1).im := by simpa using hz
    simp only [Function.comp_apply,UpperHalfPlane.ofComplex_apply_of_im_pos hz,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz1]
    have he : (⟨z+1,hz1⟩:ℍ)=(1:ℝ) +ᵥ (⟨z,hz⟩:ℍ) := by
      apply UpperHalfPlane.ext
      simp only [UpperHalfPlane.coe_vadd,Complex.ofReal_one]
      ring
    rw [he,hf]
  · have hz0 : z.im≤0 := le_of_not_gt hz
    have hz1 : (z+1).im≤0 := by simpa using hz0
    simp only [Function.comp_apply,UpperHalfPlane.ofComplex_apply_of_im_nonpos hz0,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hz1]
end QEC.Coding.TannerLiftedProduct
