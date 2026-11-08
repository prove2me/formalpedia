-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.toPGL_lpsPSLWordProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:05:14.72107+00:00
-- url     : https://prove2.me/submissions/54efab1b-438d-44b6-9b17-19806c571bbb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionAwayPGL_wordProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPGLHeckeLabel_eq_toPGL
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsPGLHeckeLabel_eq_toPGL



set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (word : List (LPSGeneratorIndex p)) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL
        (lpsPSLWordProduct a word) =
      lpsQuaternionAwayPGL a.q (lpsQuaternionAwayWordProduct a word) := by
  rw [lpsPSLWordProduct, map_list_prod,
    lpsQuaternionAwayPGL_wordProduct]
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _ht
  exact lpsPGLHeckeLabel_eq_toPGL a t |>.symm
end QEC.Coding.TannerLiftedProduct
