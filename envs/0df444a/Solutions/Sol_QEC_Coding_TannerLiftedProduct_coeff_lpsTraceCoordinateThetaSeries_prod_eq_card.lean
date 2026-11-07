-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_lpsTraceCoordinateThetaSeries_prod_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:39:38.701383+00:00
-- url     : https://prove2.me/submissions/9397f1f8-f5ee-448e-8ff3-96edc917f409

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
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
    (q n : ℕ) :
    PowerSeries.coeff n
        (∏ i : Fin 4, lpsTraceCoordinateThetaSeries q i) =
      Fintype.card (LPSTraceThetaWitness q n) := by
  rw [PowerSeries.coeff_prod]
  simp only [coeff_lpsTraceCoordinateThetaSeries, Fintype.card_sigma,
    Fintype.card_pi, Fintype.card_coe]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro l hl
  simp
end QEC.Coding.TannerLiftedProduct
