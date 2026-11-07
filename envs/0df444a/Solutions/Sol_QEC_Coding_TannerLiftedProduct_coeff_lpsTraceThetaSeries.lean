-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:36:21.048102+00:00
-- url     : https://prove2.me/submissions/4f429ae3-79c7-4ae5-9cdf-4f7fd5df4cc0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q n : ℕ) :
    PowerSeries.coeff n (lpsTraceThetaSeries q) =
      (lpsTraceQuadraticShell q n).card := by
  simp [lpsTraceThetaSeries]
end QEC.Coding.TannerLiftedProduct
