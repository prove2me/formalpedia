-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tsum_coeff_lpsTraceThetaSeries_eq_lpsStandardTheta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:46:13.997905+00:00
-- url     : https://prove2.me/submissions/db6ae751-1c1d-4fcd-a080-f322b4d27a72

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_coeff_lpsTraceThetaSeries_eq_lpsAnalyticThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (r : ℕ) (hr : 0 < r) (z : ℂ) (hz : 0 < z.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * z) ^ n) =
      lpsStandardTheta r z := by
  have hUpper : 0 < ((2 : ℂ) * z).im := by
    rw [Complex.mul_im]
    simpa using (mul_pos (by norm_num : (0 : ℝ) < 2) hz)
  have hExp : Complex.exp (Real.pi * Complex.I * ((2 : ℂ) * z)) =
      Complex.exp (2 * Real.pi * Complex.I * z) := by
    congr 1
    ring
  simpa only [lpsStandardTheta, hExp] using
    tsum_coeff_lpsTraceThetaSeries_eq_lpsAnalyticThetaProduct
      r hr (2 * z) hUpper
end QEC.Coding.TannerLiftedProduct
