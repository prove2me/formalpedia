-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsTraceThetaSeries_eq_coordinateProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:41:20.502206+00:00
-- url     : https://prove2.me/submissions/d29892e6-3e05-43c5-9b9a-33e1d6a5108a

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceCoordinateThetaSeries_prod_eq_card
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {q : ℕ} (hq : 0 < q) :
    lpsTraceThetaSeries q =
      ∏ i : Fin 4, lpsTraceCoordinateThetaSeries q i := by
  apply PowerSeries.ext
  intro n
  rw [coeff_lpsTraceThetaSeries,
    coeff_lpsTraceCoordinateThetaSeries_prod_eq_card]
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (lpsTraceThetaWitnessEquivShell hq) |>.symm
end QEC.Coding.TannerLiftedProduct
