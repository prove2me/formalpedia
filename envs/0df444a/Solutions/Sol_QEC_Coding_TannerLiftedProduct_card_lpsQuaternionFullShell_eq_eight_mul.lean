-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_eight_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:35:05.414073+00:00
-- url     : https://prove2.me/submissions/14311f7d-530a-4a96-be78-96380d1559b9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
import Mathlib.NumberTheory.Multiplicity
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : 0 < p) (hp4 : p % 4 = 1) :
    (lpsQuaternionFullShell p).card =
      8 * (lpsQuaternionShell p).card := by
  have hcard := Fintype.card_congr
    (normalizedQuaternionPlacementEquiv hp hp4)
  calc
    (lpsQuaternionFullShell p).card =
        4 * (2 * (lpsQuaternionShell p).card) := by
      simpa [Fintype.card_prod] using hcard.symm
    _ = 8 * (lpsQuaternionShell p).card := by ring
end QEC.Coding.TannerLiftedProduct
