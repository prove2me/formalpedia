-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.theta_scaled_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:40:23.340201+00:00
-- url     : https://prove2.me/submissions/ac8ec0df-c779-4db8-9ef1-fe840ee970a4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
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
theorem _root_.solution (c : ℝ) (hc : 0 < c) (z : ℂ) (hz : 0 < z.im) :
    jacobiTheta ((c : ℂ) * (-1 / z)) =
      (-Complex.I * (z / (c : ℂ))) ^ (1 / 2 : ℂ) * jacobiTheta (z / (c : ℂ)) := by
  have hn : (c : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  have zn : z ≠ 0 := by intro h; simp [h] at hz
  let τ : UpperHalfPlane := ⟨z / (c : ℂ), by simpa [Complex.div_ofReal_im] using div_pos hz hc⟩
  have h := jacobiTheta_S_smul τ
  simp only [UpperHalfPlane.modular_S_smul] at h
  dsimp [τ] at h
  convert h using 1
  congr 1
  field_simp
end QEC.Coding.TannerLiftedProduct
