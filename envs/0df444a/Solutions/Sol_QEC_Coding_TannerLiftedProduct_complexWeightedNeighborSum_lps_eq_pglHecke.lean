-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.complexWeightedNeighborSum_lps_eq_pglHecke
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:42:58.956222+00:00
-- url     : https://prove2.me/submissions/837c4a7e-1542-4f74-900c-8bc4d289b985

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyRightTranslationSum_lps_eq_pglHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_complexWeightedNeighborSum_rightCayleyGraph


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p)
    (f : PGL(2, ZMod a.q) → ℂ)
    (g : PSL(2, ZMod a.q)) :
    SmallSetExpansion.complexWeightedNeighborSum
        (rightCayleyGraph (lpsQuaternionLabel a))
        (fun h => f (Matrix.ProjectiveSpecialLinearGroup.toPGL h)) g =
      cayleyRightTranslationSum (lpsPGLHeckeLabel a) f
        (Matrix.ProjectiveSpecialLinearGroup.toPGL g) := by
  rw [complexWeightedNeighborSum_rightCayleyGraph]
  exact cayleyRightTranslationSum_lps_eq_pglHecke a f g
end QEC.Coding.TannerLiftedProduct
