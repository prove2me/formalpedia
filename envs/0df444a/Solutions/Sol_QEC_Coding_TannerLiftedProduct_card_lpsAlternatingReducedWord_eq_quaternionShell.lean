-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsAlternatingReducedWord_eq_quaternionShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:22:04.831693+00:00
-- url     : https://prove2.me/submissions/67c1e1ee-daa4-415e-ab32-483a339eb21a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_fintype_card_lpsAlternatingReducedWord
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_prime_pow_eq_alternatingReducedWordCount


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    Fintype.card (LPSAlternatingReducedWord a.degreePrime.pos n) =
      Fintype.card {t // t ∈ lpsQuaternionShell (p ^ n)} := by
  rw [fintype_card_lpsAlternatingReducedWord,
    Fintype.card_coe,
    card_lpsQuaternionShell_prime_pow_eq_alternatingReducedWordCount
      a.degreePrime a.degreeModFour]
end QEC.Coding.TannerLiftedProduct
