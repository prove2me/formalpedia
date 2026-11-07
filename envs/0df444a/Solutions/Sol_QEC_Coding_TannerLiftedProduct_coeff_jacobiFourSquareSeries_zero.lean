-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:35:52.007989+00:00
-- url     : https://prove2.me/submissions/26198f5c-ad3f-4cfb-b84d-fb06e8305e5b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    PowerSeries.coeff 0 jacobiFourSquareSeries = 1 := by
  simp [jacobiFourSquareSeries]
end QEC.Coding.TannerLiftedProduct
