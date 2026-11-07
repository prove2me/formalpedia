-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tsum_coeff_lpsTraceThetaSeries_eq_lpsAnalyticThetaProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:45:04.180091+00:00
-- url     : https://prove2.me/submissions/30b4ffc0-a322-46d5-89f2-c1775345b2a2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tsum_coeff_lpsTraceThetaSeries_eq_jacobiTheta_product

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (r : ℕ) (hr : 0 < r) (τ : ℂ) (hτ : 0 < τ.im) :
    (∑' n : ℕ,
      ((PowerSeries.coeff n (lpsTraceThetaSeries r) : ℕ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * τ) ^ n) =
      lpsAnalyticThetaProduct r τ := by
  exact tsum_coeff_lpsTraceThetaSeries_eq_jacobiTheta_product r hr τ hτ
end QEC.Coding.TannerLiftedProduct
