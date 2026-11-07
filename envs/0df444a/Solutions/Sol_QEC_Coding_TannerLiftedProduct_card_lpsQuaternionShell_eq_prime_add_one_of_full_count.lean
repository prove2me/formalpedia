-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsQuaternionShell_eq_prime_add_one_of_full_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:36:25.802898+00:00
-- url     : https://prove2.me/submissions/4cd34371-1c34-47e1-8b87-d2531f812151

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
import Mathlib.NumberTheory.Multiplicity
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionFullShell_eq_eight_mul

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : 0 < p) (hp4 : p % 4 = 1)
    (hFull : (lpsQuaternionFullShell p).card = 8 * (p + 1)) :
    (lpsQuaternionShell p).card = p + 1 := by
  have hEight := card_lpsQuaternionFullShell_eq_eight_mul hp hp4
  omega
end QEC.Coding.TannerLiftedProduct
