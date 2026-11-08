-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFinQuaternionFamilyLabel_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:41:16.418418+00:00
-- url     : https://prove2.me/submissions/0b8718ee-aeb9-4b71-b7d8-9fa93b852c6a

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionFamilyLabel_injective

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ) :
    Function.Injective (lpsFinQuaternionFamilyLabel hp hp4 hCount n) :=
  (lpsQuaternionFamilyLabel_injective hp hp4 n).comp
    (lpsFinGeneratorEquiv hCount).injective
end QEC.Coding.TannerLiftedProduct
