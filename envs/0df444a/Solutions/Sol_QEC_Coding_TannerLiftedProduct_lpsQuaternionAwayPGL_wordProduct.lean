-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionAwayPGL_wordProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:02:11.936804+00:00
-- url     : https://prove2.me/submissions/93abf436-a68b-4fc2-9a5e-b336fc78e63b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (word : List (LPSGeneratorIndex p)) :
    lpsQuaternionAwayPGL a.q (lpsQuaternionAwayWordProduct a word) =
      (word.map (lpsPGLHeckeLabel a)).prod := by
  change lpsQuaternionAwayPGL a.q
      ((word.map (lpsQuaternionShellAwayLabel a)).prod) = _
  rw [map_list_prod]
  rw [List.map_map]
  change (word.map (lpsPGLHeckeLabel a)).prod = _
  rfl
end QEC.Coding.TannerLiftedProduct
