-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_integerThetaSeries_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:37:53.650735+00:00
-- url     : https://prove2.me/submissions/264d2fb5-59c6-450c-81c9-b7f755e81dde

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_integerSquareRoots_sq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) (hm : 0 < m) :
    PowerSeries.coeff (m ^ 2) integerThetaSeries = 2 := by
  simp [card_integerSquareRoots_sq m hm]
end QEC.Coding.TannerLiftedProduct
