-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionGL_eq_away
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:47:21.865974+00:00
-- url     : https://prove2.me/submissions/bf4ee6ce-84f0-4c99-b551-1baf2c8362ed

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionGL a t ht =
      lpsQuaternionAwayGL a.q (lpsQuaternionAwayElement a t ht) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl
end QEC.Coding.TannerLiftedProduct
