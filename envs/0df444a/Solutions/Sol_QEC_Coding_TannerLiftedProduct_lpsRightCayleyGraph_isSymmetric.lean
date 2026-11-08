-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsRightCayleyGraph_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:03:44.046189+00:00
-- url     : https://prove2.me/submissions/597df351-c3d7-4902-b9f3-8c545c955f5b

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightCayleyGraph_lpsQuaternionLabel_isSymmetric

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    SmallSetExpansion.IsSymmetric
      (rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n)) := by
  exact rightCayleyGraph_lpsQuaternionLabel_isSymmetric
    (lpsResiduePrimeSequence hp hp4 n)
end QEC.Coding.TannerLiftedProduct
