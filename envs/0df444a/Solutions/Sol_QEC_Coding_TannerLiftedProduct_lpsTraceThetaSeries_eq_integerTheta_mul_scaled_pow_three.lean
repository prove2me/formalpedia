-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:42:21.438698+00:00
-- url     : https://prove2.me/submissions/2a2324fc-9453-4c1f-bff7-0565d6da19b9

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceThetaSeries_eq_coordinateProduct
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
    {q : ℕ} (hq : 0 < q) :
    lpsTraceThetaSeries q =
      integerThetaSeries * scaledIntegerThetaSeries (2 * q) ^ 3 := by
  rw [lpsTraceThetaSeries_eq_coordinateProduct hq]
  simp [lpsTraceCoordinateThetaSeries, lpsTraceCoordinateRoots,
    integerThetaSeries, scaledIntegerThetaSeries, Fin.prod_univ_four]
  ring
end QEC.Coding.TannerLiftedProduct
