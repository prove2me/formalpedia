-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPGLHeckeLabel_eq_toPGL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:43:07.380064+00:00
-- url     : https://prove2.me/submissions/7dcad6d2-5944-484a-8f71-a42d16f5b000

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionPGL_eq_away
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_toPGL_lpsQuaternionPSL


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (t : LPSGeneratorIndex p) :
    lpsPGLHeckeLabel a t =
      Matrix.ProjectiveSpecialLinearGroup.toPGL
        (lpsQuaternionLabel a t) := by
  rw [lpsPGLHeckeLabel, lpsQuaternionShellAwayLabel,
    lpsQuaternionLabel, toPGL_lpsQuaternionPSL,
    lpsQuaternionPGL_eq_away]
end QEC.Coding.TannerLiftedProduct
