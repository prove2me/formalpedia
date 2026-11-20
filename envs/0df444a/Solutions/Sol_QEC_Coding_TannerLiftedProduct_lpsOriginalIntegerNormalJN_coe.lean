-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalJN_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:58:12.544181+00:00
-- url     : https://prove2.me/submissions/c377d444-113e-43ed-a128-0ed6e805ed1a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerAffineToNormal_root


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    (lpsOriginalIntegerNormalJN N hN).val.val =
      lpsOriginalJNInFractionField N hN := by
  exact lpsOriginalIntegerAffineToNormal_root N hN
end QEC.Coding.TannerLiftedProduct
