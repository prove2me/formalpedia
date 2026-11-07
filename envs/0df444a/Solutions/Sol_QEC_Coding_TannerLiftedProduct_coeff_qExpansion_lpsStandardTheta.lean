-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsStandardTheta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:56:51.042888+00:00
-- url     : https://prove2.me/submissions/27353a3e-5cba-48fa-8186-a8bfa606641f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_add_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasSum_lpsStandardTheta_coeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


section
namespace QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold
private theorem lpsStandardTheta_periodic_comp_ofComplex (r : ℕ) :
    Function.Periodic
      ((fun z : ℍ => lpsStandardTheta r z) ∘ UpperHalfPlane.ofComplex) 1 := by
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz1]
    exact lpsStandardTheta_add_one r z
  · have hz0 : z.im ≤ 0 := le_of_not_gt hz
    have hz1 : (z + 1).im ≤ 0 := by simpa using hz0
    simp only [Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hz0,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hz1]
private theorem hasSum_lpsStandardTheta_coeff_smul
    (r : ℕ) (hr : 0 < r) (z : ℍ) :
    HasSum (fun m : ℕ =>
      ((PowerSeries.coeff m (lpsTraceThetaSeries r) : ℕ) : ℂ) •
        Function.Periodic.qParam 1 (z : ℂ) ^ m)
      (lpsStandardTheta r z) := by
  simpa only [smul_eq_mul] using hasSum_lpsStandardTheta_coeff r hr z
private theorem boundedAtImInfty_lpsStandardTheta
    (r : ℕ) (hr : 0 < r) :
    UpperHalfPlane.IsBoundedAtImInfty
      (fun z : ℍ => lpsStandardTheta r z) := by
  apply UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion
    (by norm_num : (0 : ℝ) < 1)
  exact hasSum_lpsStandardTheta_coeff_smul r hr
private theorem analyticAt_cuspFunction_lpsStandardTheta
    (r : ℕ) (hr : 0 < r) :
    AnalyticAt ℂ
      (UpperHalfPlane.cuspFunction 1
        (fun z : ℍ => lpsStandardTheta r z)) 0 := by
  exact UpperHalfPlane.analyticAt_cuspFunction_zero
    (by norm_num : (0 : ℝ) < 1)
    (lpsStandardTheta_periodic_comp_ofComplex r)
    (mdifferentiable_lpsStandardTheta r hr)
    (boundedAtImInfty_lpsStandardTheta r hr)
end QEC.Coding.TannerLiftedProduct
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (r : ℕ) (hr : 0 < r) (n : ℕ) :
    PowerSeries.coeff n
        (UpperHalfPlane.qExpansion 1
          (fun z : ℍ => lpsStandardTheta r z)) =
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) := by
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique
    (lpsStandardThetaContinuousMap r hr)
    (by norm_num : (0 : ℝ) < 1)
    (analyticAt_cuspFunction_lpsStandardTheta r hr)
    (hasSum_lpsStandardTheta_coeff_smul r hr) n
end QEC.Coding.TannerLiftedProduct
