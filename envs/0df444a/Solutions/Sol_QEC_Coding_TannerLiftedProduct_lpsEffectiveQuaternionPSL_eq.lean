-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionPSL_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:55:07.777207+00:00
-- url     : https://prove2.me/submissions/b86a8342-53cc-4cb1-b615-8c7db947a523

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_toPGL_lpsEffectiveQuaternionPSL
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_toPGL_lpsQuaternionPSL


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsEffectiveQuaternionPSL a t ht = lpsQuaternionPSL a t ht := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_lpsEffectiveQuaternionPSL, toPGL_lpsQuaternionPSL]
end QEC.Coding.TannerLiftedProduct
