-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.map_scaledIntegerThetaSeries_eq_subst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:40:33.493192+00:00
-- url     : https://prove2.me/submissions/a88bfb9f-738e-42a4-bc9e-6563fd2bdf62

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_scaledIntegerSquareRoots_eq_of_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_scaledIntegerSquareRoots_eq_empty_of_not_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {m : ℕ} (hm : 0 < m) :
    (scaledIntegerThetaSeries m).map (Nat.castRingHom ℤ) =
      PowerSeries.subst (PowerSeries.X ^ (m ^ 2))
        (integerThetaSeries.map (Nat.castRingHom ℤ)) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, coeff_scaledIntegerThetaSeries,
    PowerSeries.coeff_subst_X_pow (pow_ne_zero 2 hm.ne')]
  by_cases hdiv : m ^ 2 ∣ n
  · rw [if_pos hdiv, scaledIntegerSquareRoots_eq_of_dvd hm hdiv,
      PowerSeries.coeff_map, coeff_integerThetaSeries]
    simp
  · rw [if_neg hdiv, scaledIntegerSquareRoots_eq_empty_of_not_dvd hm hdiv]
    simp
end QEC.Coding.TannerLiftedProduct
