-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_integerThetaSeries_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:39:37.620907+00:00
-- url     : https://prove2.me/submissions/1e072f1b-5b28-4067-8b70-62b06feb7f62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_integerSquareRoots

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) :
    PowerSeries.coeff n integerThetaSeries =
      if n = 0 then 1 else if IsSquare n then 2 else 0 := by
  rw [coeff_integerThetaSeries, card_integerSquareRoots]
end QEC.Coding.TannerLiftedProduct
