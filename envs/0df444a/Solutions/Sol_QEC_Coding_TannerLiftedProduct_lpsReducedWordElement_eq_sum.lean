-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:29:33.631023+00:00
-- url     : https://prove2.me/submissions/00463e44-8f80-4d87-a206-6d6614ccb3e9

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_lpsReducedWords_iff

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsReducedWordElement a n =
      ∑ word : LPSReducedWord a.degreePrime.pos n,
        MonoidAlgebra.single
          (cayleyVectorWordProduct (lpsQuaternionLabel a) word.1) 1 := by
  classical
  rw [lpsReducedWordElement]
  exact Finset.sum_subtype
    (lpsReducedWords a.degreePrime.pos n)
    (fun word => mem_lpsReducedWords_iff _ word)
    (fun word => MonoidAlgebra.single
      (cayleyVectorWordProduct (lpsQuaternionLabel a) word) 1)
end QEC.Coding.TannerLiftedProduct
