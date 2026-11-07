-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries_eq_congruenceShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:37:35.190602+00:00
-- url     : https://prove2.me/submissions/b7b3778a-a851-41de-9f10-1ccfd70a86cd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsTraceQuadraticShell_eq_congruenceShell
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    PowerSeries.coeff n (lpsTraceThetaSeries q) =
      (lpsTraceCongruenceShell q n).card := by
  rw [coeff_lpsTraceThetaSeries,
    card_lpsTraceQuadraticShell_eq_congruenceShell hq hn]
end QEC.Coding.TannerLiftedProduct
