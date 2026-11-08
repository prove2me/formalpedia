-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:45:36.242197+00:00
-- url     : https://prove2.me/submissions/a7eb3974-5435-4bd7-8be4-78c48971670d

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_eq_fintype_card
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_fintype_card_lpsReducedWord_add_two

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    (lpsReducedWords hp.pos (n + 2)).card =
      p * (lpsReducedWords hp.pos (n + 1)).card := by
  rw [card_lpsReducedWords_eq_fintype_card,
    card_lpsReducedWords_eq_fintype_card,
    fintype_card_lpsReducedWord_add_two hp hp4]
end QEC.Coding.TannerLiftedProduct
