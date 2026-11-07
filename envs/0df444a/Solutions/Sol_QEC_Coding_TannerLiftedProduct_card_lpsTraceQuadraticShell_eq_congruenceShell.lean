-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_eq_congruenceShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:36:22.497206+00:00
-- url     : https://prove2.me/submissions/21499f8c-3c8b-416d-ab12-f70cbd870812

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    (lpsTraceQuadraticShell q n).card =
      (lpsTraceCongruenceShell q n).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr
    (lpsTraceQuadraticShellEquivCongruenceShell hq hn)
end QEC.Coding.TannerLiftedProduct
