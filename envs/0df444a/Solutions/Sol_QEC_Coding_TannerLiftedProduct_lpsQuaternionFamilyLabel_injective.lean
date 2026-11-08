-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionFamilyLabel_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:57:39.870192+00:00
-- url     : https://prove2.me/submissions/c1cf3d38-256d-42a4-9faa-a06eb74de731

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionLabel_injective

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Function.Injective (lpsQuaternionFamilyLabel hp hp4 n) :=
  lpsQuaternionLabel_injective (lpsResiduePrimeSequence hp hp4 n)
end QEC.Coding.TannerLiftedProduct
