-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rightCayleyGraph_lpsFinQuaternionFamilyLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:59:01.655123+00:00
-- url     : https://prove2.me/submissions/693de3b7-80cd-4aaf-94fd-edf7a2ac3b2f

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightCayleyGraph_reindex


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ) :
    rightCayleyGraph (lpsFinQuaternionFamilyLabel hp hp4 hCount n) =
      rightCayleyGraph (lpsQuaternionFamilyLabel hp hp4 n) :=
  rightCayleyGraph_reindex
    (lpsQuaternionFamilyLabel hp hp4 n) (lpsFinGeneratorEquiv hCount)
end QEC.Coding.TannerLiftedProduct
