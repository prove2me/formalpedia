-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPetersson_fundamentalDomain_volume_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:08:31.059205+00:00
-- url     : https://prove2.me/submissions/af243bdf-d50c-4664-86fc-f456cd428440

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPetersson_complex_strip_inverse_square_integrable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : (volume : Measure ℍ) ModularGroup.fd < ⊤ := by
  let S : Set ℂ := Complex.measurableEquivRealProd ⁻¹'
    (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (1/2:ℝ))
  have hsub : UpperHalfPlane.coe '' ModularGroup.fd ⊆ S := by
    rintro z ⟨τ,hτ,rfl⟩
    have hxy := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
    have hr := abs_le.mp hτ.2
    change (τ.re,τ.im) ∈ Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (1/2:ℝ)
    exact ⟨⟨by linarith [hr.1],hr.2⟩,by change (1/2:ℝ)<τ.im; have hp := τ.im_pos; nlinarith⟩
  rw [UpperHalfPlane.volume_eq_lintegral]
  apply lt_of_le_of_lt (lintegral_mono_set hsub)
  have hi := lpsPetersson_complex_strip_inverse_square_integrable
  have hfinite := hi.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfinite
  convert hfinite using 1
  apply setLIntegral_congr_fun ((measurableSet_Icc.prod measurableSet_Ioi).preimage
    Complex.measurableEquivRealProd.measurable)
  intro z hz
  change (z.re,z.im) ∈ Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (1/2:ℝ) at hz
  have hzpos : 0<z.im := by have h : (1/2:ℝ)<z.im := hz.2;linarith
  simp only [enorm_eq_nnnorm,nnnorm_pow,nnnorm_div,nnnorm_one]
end QEC.Coding.TannerLiftedProduct
