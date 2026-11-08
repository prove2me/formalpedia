-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.trace_lpsFiniteHeckeElement_eq_alternatingClosedReducedWordCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:43:33.854503+00:00
-- url     : https://prove2.me/submissions/d85fd5ca-7002-49a4-98aa-6f1eedc50e16

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsFiniteHeckeElement_one_eq_alternatingClosedReducedWordCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_lpsFiniteHeckeElement


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
        (cayleyRightRegularRepresentation.asAlgebraHom
          (lpsFiniteHeckeElement a n)) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
        (lpsAlternatingClosedReducedWordCount a n : ℂ) := by
  rw [trace_lpsFiniteHeckeElement,
    coeff_lpsFiniteHeckeElement_one_eq_alternatingClosedReducedWordCount]
end QEC.Coding.TannerLiftedProduct
