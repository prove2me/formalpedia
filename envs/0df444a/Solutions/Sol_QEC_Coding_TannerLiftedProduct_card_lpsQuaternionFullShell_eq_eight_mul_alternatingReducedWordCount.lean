-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_eight_mul_alternatingReducedWordCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:12:36.794074+00:00
-- url     : https://prove2.me/submissions/a91e4d93-50f0-4015-a12e-0c4ae2af74cc

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionFullShell_eq_prime_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordCount_eq_geomSum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    (lpsQuaternionFullShell (p ^ n)).card =
      8 * lpsAlternatingReducedWordCount hp.pos n := by
  rw [card_lpsQuaternionFullShell_eq_prime_pow hp hp4,
    lpsAlternatingReducedWordCount_eq_geomSum hp hp4]
end QEC.Coding.TannerLiftedProduct
