-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_eq_fintype_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:25:18.758554+00:00
-- url     : https://prove2.me/submissions/f6babac0-40ab-4772-979d-aa4f3b33be55

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : 0 < p) (n : ℕ) :
    (lpsReducedWords hp n).card =
      Fintype.card (LPSReducedWord hp n) := by
  classical
  rw [Fintype.card_subtype]
  rfl
end QEC.Coding.TannerLiftedProduct
