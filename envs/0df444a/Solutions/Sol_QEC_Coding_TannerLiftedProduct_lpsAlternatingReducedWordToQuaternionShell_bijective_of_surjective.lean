-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordToQuaternionShell_bijective_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:24:56.815533+00:00
-- url     : https://prove2.me/submissions/4f9331b2-c320-46bd-bc2a-1a95044fdac2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsAlternatingReducedWord_eq_quaternionShell

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    Function.Bijective (lpsAlternatingReducedWordToQuaternionShell a n) := by
  exact (Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨hsurj, card_lpsAlternatingReducedWord_eq_quaternionShell a n⟩
end QEC.Coding.TannerLiftedProduct
