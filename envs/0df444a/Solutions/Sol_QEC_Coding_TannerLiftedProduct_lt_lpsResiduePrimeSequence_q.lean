-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lt_lpsResiduePrimeSequence_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:56:56.334702+00:00
-- url     : https://prove2.me/submissions/a8f1fecf-afb1-436c-b041-4a1a9244dfa7

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lt_lpsResiduePrimeAt


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    n < (lpsResiduePrimeSequence hp hp4 n).q :=
  lt_lpsResiduePrimeAt hp hp4 n
end QEC.Coding.TannerLiftedProduct
