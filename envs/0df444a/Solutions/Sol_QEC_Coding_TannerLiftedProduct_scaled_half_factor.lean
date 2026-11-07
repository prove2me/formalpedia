-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.scaled_half_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:41:32.008736+00:00
-- url     : https://prove2.me/submissions/a4a960b0-7c9f-40e4-ae96-546f160ffa3f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cpow_pos_real_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ≠ 0) :
    (((r : ℂ)^2) * z) ^ (1 / 2 : ℂ) = (r : ℂ) * z ^ (1 / 2 : ℂ) := by
  have hp : 0 < r^2 := sq_pos_of_pos hr
  have h := cpow_pos_real_mul (r^2) hp z (1/2) hz
  simp only [Complex.ofReal_pow] at h
  rw [h]
  have hh : ((r : ℂ)^2) ^ (1/2 : ℂ) = (r : ℂ) := by
    simpa only [one_div] using Complex.sq_cpow_two_inv (x := (r : ℂ)) (by simpa using hr)
  rw [hh]
end QEC.Coding.TannerLiftedProduct
