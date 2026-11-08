-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFinRightCayleyGraph_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:06:57.496972+00:00
-- url     : https://prove2.me/submissions/fae4e100-d481-4d5c-be05-9f59f0f4e9e7

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightCayleyGraph_lpsFinQuaternionFamilyLabel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRightCayleyGraph_isSymmetric

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ) :
    SmallSetExpansion.IsSymmetric
      (rightCayleyGraph (lpsFinQuaternionFamilyLabel hp hp4 hCount n)) := by
  rw [rightCayleyGraph_lpsFinQuaternionFamilyLabel hp hp4 hCount n]
  exact lpsRightCayleyGraph_isSymmetric hp hp4 n
end QEC.Coding.TannerLiftedProduct
