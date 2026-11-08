-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionLabel_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:44:47.32159+00:00
-- url     : https://prove2.me/submissions/62fd770b-e7cb-4337-b8dc-b83e88ae6e5e

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionPSL_injective


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : LPSResiduePrime p) :
    Function.Injective (lpsQuaternionLabel a) :=
  lpsQuaternionPSL_injective a
end QEC.Coding.TannerLiftedProduct
