-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_traceCongruenceShell_eq_two_mul_alternatingClosedCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:26:24.605947+00:00
-- url     : https://prove2.me/submissions/f6ccd84b-e0da-4bcf-ad7b-f6139a084e9a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordToQuaternionShell_surjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_traceCongruenceShell_eq_two_mul_alternatingClosedCount_of_surjective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsTraceCongruenceShell a.q (p ^ n)).card =
      2 * lpsAlternatingClosedReducedWordCount a n :=
  card_traceCongruenceShell_eq_two_mul_alternatingClosedCount_of_surjective
    a n (lpsAlternatingReducedWordToQuaternionShell_surjective a n)
end QEC.Coding.TannerLiftedProduct
