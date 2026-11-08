-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_traceCongruenceShell_eq_two_mul_alternatingClosedCount_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:45:03.507382+00:00
-- url     : https://prove2.me/submissions/d90dcdde-7c38-4988-adbb-551920dfbb73

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_traceCongruenceShell_eq_two_mul_normalizedTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_fintype_card_lpsClosedAlternatingReducedWord

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    (lpsTraceCongruenceShell a.q (p ^ n)).card =
      2 * lpsAlternatingClosedReducedWordCount a n := by
  rw [card_traceCongruenceShell_eq_two_mul_normalizedTrace]
  congr 1
  rw [← fintype_card_lpsClosedAlternatingReducedWord a n]
  exact Fintype.card_congr
    (lpsClosedAlternatingReducedWordEquivNormalizedTrace a n hsurj).symm
end QEC.Coding.TannerLiftedProduct
