-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsReducedSuccessors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:25:51.771874+00:00
-- url     : https://prove2.me/submissions/d8b2ca06-469e-404d-afa0-816e048f2f24

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (t : LPSGeneratorIndex p) :
    (lpsReducedSuccessors hp.pos t).card = p := by
  rw [lpsReducedSuccessors, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, card_lpsGeneratorIndex,
    card_lpsQuaternionShell_eq_prime_add_one hp hp4]
  omega
end QEC.Coding.TannerLiftedProduct
