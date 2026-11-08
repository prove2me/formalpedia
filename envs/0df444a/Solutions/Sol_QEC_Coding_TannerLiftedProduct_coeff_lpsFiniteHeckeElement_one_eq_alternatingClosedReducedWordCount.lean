-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_lpsFiniteHeckeElement_one_eq_alternatingClosedReducedWordCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:21:09.191809+00:00
-- url     : https://prove2.me/submissions/449e0325-8a27-4e8f-9190-30dd827a0d28

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_eq_lpsAlternatingReducedWordElement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsAlternatingReducedWordElement_one


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsFiniteHeckeElement a n).coeff 1 =
      (lpsAlternatingClosedReducedWordCount a n : ℂ) := by
  rw [lpsFiniteHeckeElement_eq_lpsAlternatingReducedWordElement,
    coeff_lpsAlternatingReducedWordElement_one]
end QEC.Coding.TannerLiftedProduct
