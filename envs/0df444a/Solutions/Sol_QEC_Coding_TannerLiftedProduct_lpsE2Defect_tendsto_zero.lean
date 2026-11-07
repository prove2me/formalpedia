-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2Defect_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:01:58.597738+00:00
-- url     : https://prove2.me/submissions/97285dd8-8592-4ac6-81ce-7fa41521dad8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRealShiftInverse_tendsto_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (γ : SL(2,ℤ)) :
    Tendsto (EisensteinSeries.D2 γ) UpperHalfPlane.atImInfty (𝓝 0) := by
  by_cases hc : γ 1 0=0
  · have he : EisensteinSeries.D2 γ=(fun z : ℍ => (0:ℂ)) := by
      funext z
      simp [EisensteinSeries.D2,hc]
    rw [he]
    exact tendsto_const_nhds
  · have hcC : (γ 1 0:ℂ)≠0 := by exact_mod_cast hc
    have he : EisensteinSeries.D2 γ = (fun z : ℍ =>
        (2*Real.pi*Complex.I:ℂ)*((z:ℂ)+(((γ 1 1:ℝ)/(γ 1 0:ℝ)):ℂ))⁻¹) := by
      funext z
      rw [EisensteinSeries.D2,ModularGroup.denom_apply]
      simp only [Complex.ofReal_intCast]
      field_simp [hcC]
    rw [he]
    simpa only [Complex.ofReal_div,Complex.ofReal_intCast,mul_zero] using
      (lpsRealShiftInverse_tendsto_zero ((γ 1 1:ℝ)/(γ 1 0:ℝ))).const_mul
        (2*Real.pi*Complex.I:ℂ)
end QEC.Coding.TannerLiftedProduct
