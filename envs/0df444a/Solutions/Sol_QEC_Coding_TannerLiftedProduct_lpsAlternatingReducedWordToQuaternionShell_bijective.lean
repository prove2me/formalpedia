-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordToQuaternionShell_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:43:44.000014+00:00
-- url     : https://prove2.me/submissions/e824b7c6-262e-412b-a2bf-15a3f64da964

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordToQuaternionShell_surjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordToQuaternionShell_bijective_of_surjective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    Function.Bijective
      (lpsAlternatingReducedWordToQuaternionShell a n) :=
  lpsAlternatingReducedWordToQuaternionShell_bijective_of_surjective
    a n (lpsAlternatingReducedWordToQuaternionShell_surjective a n)
end QEC.Coding.TannerLiftedProduct
