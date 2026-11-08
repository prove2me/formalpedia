-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.fintype_card_lpsAlternatingReducedWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:05:13.658693+00:00
-- url     : https://prove2.me/submissions/1a52f0db-653a-45e1-bb45-5292115a9e40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_eq_fintype_card


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : 0 < p) (n : ℕ) :
    Fintype.card (LPSAlternatingReducedWord hp n) =
      lpsAlternatingReducedWordCount hp n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      change Fintype.card (LPSReducedWord hp 0) =
        (lpsReducedWords hp 0).card
      exact (card_lpsReducedWords_eq_fintype_card hp 0).symm
  | one =>
      change Fintype.card (LPSReducedWord hp 1) =
        (lpsReducedWords hp 1).card
      exact (card_lpsReducedWords_eq_fintype_card hp 1).symm
  | more n hn _hnOne =>
      change Fintype.card
          (LPSReducedWord hp (n + 2) ⊕ LPSAlternatingReducedWord hp n) =
        (lpsReducedWords hp (n + 2)).card +
          lpsAlternatingReducedWordCount hp n
      rw [Fintype.card_sum, hn,
        card_lpsReducedWords_eq_fintype_card hp (n + 2)]
end QEC.Coding.TannerLiftedProduct
