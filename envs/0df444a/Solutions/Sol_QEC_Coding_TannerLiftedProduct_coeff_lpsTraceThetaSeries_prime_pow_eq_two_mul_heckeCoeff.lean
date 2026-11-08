-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:27:17.515204+00:00
-- url     : https://prove2.me/submissions/69f1f332-55d0-4c73-aa2d-fee69cff9f70

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordToQuaternionShell_surjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff_of_surjective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) =
      2 * (lpsFiniteHeckeElement a n).coeff 1 :=
  coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff_of_surjective
    a n (lpsAlternatingReducedWordToQuaternionShell_surjective a n)
end QEC.Coding.TannerLiftedProduct
