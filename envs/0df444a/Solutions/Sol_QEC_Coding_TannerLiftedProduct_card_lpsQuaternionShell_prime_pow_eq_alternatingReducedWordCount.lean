-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsQuaternionShell_prime_pow_eq_alternatingReducedWordCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:18:53.363484+00:00
-- url     : https://prove2.me/submissions/06b46e16-8fe7-435d-827b-3d326ee74803

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lps_prime_pow_mod_four
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionFullShell_eq_eight_mul_alternatingReducedWordCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionFullShell_eq_eight_mul


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    (lpsQuaternionShell (p ^ n)).card =
      lpsAlternatingReducedWordCount hp.pos n := by
  have hmod : p ^ n % 4 = 1 := lps_prime_pow_mod_four hp4 n
  have hfull :=
    card_lpsQuaternionFullShell_eq_eight_mul_alternatingReducedWordCount
      hp hp4 n
  have hnormalize := card_lpsQuaternionFullShell_eq_eight_mul
    (pow_pos hp.pos n) hmod
  omega
end QEC.Coding.TannerLiftedProduct
