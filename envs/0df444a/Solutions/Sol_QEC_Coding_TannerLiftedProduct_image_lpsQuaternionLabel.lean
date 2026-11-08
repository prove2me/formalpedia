-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.image_lpsQuaternionLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:40:43.503516+00:00
-- url     : https://prove2.me/submissions/1e6f6b41-362b-47a6-bfce-290571e1ae3e

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : LPSResiduePrime p) :
    Finset.univ.image (lpsQuaternionLabel a) =
      lpsQuaternionGeneratorsPSL a := by
  classical
  rfl
end QEC.Coding.TannerLiftedProduct
