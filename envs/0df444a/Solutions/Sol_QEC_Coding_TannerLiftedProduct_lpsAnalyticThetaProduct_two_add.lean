-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsAnalyticThetaProduct_two_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:40:08.531199+00:00
-- url     : https://prove2.me/submissions/6d5d5df1-5f42-4a18-b891-e5c625610de2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
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
theorem _root_.solution (r : ℕ) (τ : ℂ) :
    lpsAnalyticThetaProduct r (2 + τ) = lpsAnalyticThetaProduct r τ := by
  let m : ℕ := (2 * r) ^ 2
  have hPeriod : Function.Periodic jacobiTheta (2 : ℂ) := by
    intro z
    simpa only [add_comm] using jacobiTheta_two_add z
  have hScaled : jacobiTheta ((m : ℂ) * ((2 : ℂ) + τ)) =
      jacobiTheta ((m : ℂ) * τ) := by
    have hShift : (m : ℂ) * ((2 : ℂ) + τ) =
        (m : ℂ) * τ + (m : ℂ) * 2 := by ring
    rw [hShift]
    simpa only [Nat.cast_mul] using (hPeriod.nat_mul m) ((m : ℂ) * τ)
  unfold lpsAnalyticThetaProduct
  rw [jacobiTheta_two_add, show (((2 * r) ^ 2 : ℕ) : ℂ) = (m : ℂ) from rfl,
    hScaled]
end QEC.Coding.TannerLiftedProduct
