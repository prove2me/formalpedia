-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:48:45.143182+00:00
-- url     : https://prove2.me/submissions/0c4bac24-74dd-45f5-a1ae-c6723fcb3c8f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_traceCongruenceShell_eq_two_mul_alternatingClosedCount_of_surjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries_eq_congruenceShell


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) =
      2 * lpsAlternatingClosedReducedWordCount a n := by
  rw [coeff_lpsTraceThetaSeries_eq_congruenceShell
    a.prime.pos (pow_pos a.degreePrime.pos n)]
  exact card_traceCongruenceShell_eq_two_mul_alternatingClosedCount_of_surjective
    a n hsurj
end QEC.Coding.TannerLiftedProduct
