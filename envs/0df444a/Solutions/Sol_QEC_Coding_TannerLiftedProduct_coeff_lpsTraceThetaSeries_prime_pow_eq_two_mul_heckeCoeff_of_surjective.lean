-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:59:12.240397+00:00
-- url     : https://prove2.me/submissions/54d160b0-de8c-4540-adb6-daafe59ea2b2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount_of_surjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsFiniteHeckeElement_one_eq_alternatingClosedReducedWordCount


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) =
      2 * (lpsFiniteHeckeElement a n).coeff 1 := by
  rw [coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount_of_surjective
      a n hsurj,
    coeff_lpsFiniteHeckeElement_one_eq_alternatingClosedReducedWordCount]
  norm_cast
end QEC.Coding.TannerLiftedProduct
