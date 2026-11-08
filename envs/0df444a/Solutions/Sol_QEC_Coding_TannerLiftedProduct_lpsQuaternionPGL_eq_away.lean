-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionPGL_eq_away
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:27:05.923481+00:00
-- url     : https://prove2.me/submissions/a7229973-b520-4c5f-a2ea-47755af24ad4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionGL_eq_away

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionPGL a t ht =
      lpsQuaternionAwayPGL a.q (lpsQuaternionAwayElement a t ht) := by
  rw [lpsQuaternionPGL, lpsQuaternionAwayPGL_apply,
    lpsQuaternionGL_eq_away]
end QEC.Coding.TannerLiftedProduct
