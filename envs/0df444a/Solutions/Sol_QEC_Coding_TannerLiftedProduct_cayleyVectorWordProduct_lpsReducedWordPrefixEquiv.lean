-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.cayleyVectorWordProduct_lpsReducedWordPrefixEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:23:41.079026+00:00
-- url     : https://prove2.me/submissions/f4d25d5b-9806-480f-867c-7453d0ffccb8

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ)
    (pair : {pair : LPSGeneratorIndex p ×
        LPSReducedWord a.degreePrime.pos (n + 1) //
      pair.1 ∈ lpsReducedSuccessors
        a.degreePrime.pos pair.2.1.head}) :
    cayleyVectorWordProduct (lpsQuaternionLabel a)
        (lpsReducedWordPrefixEquiv a.degreePrime n pair).1 =
      lpsQuaternionLabel a pair.1.1 *
        cayleyVectorWordProduct (lpsQuaternionLabel a) pair.1.2.1 := by
  exact cayleyVectorWordProduct_cons _ _ _
end QEC.Coding.TannerLiftedProduct
