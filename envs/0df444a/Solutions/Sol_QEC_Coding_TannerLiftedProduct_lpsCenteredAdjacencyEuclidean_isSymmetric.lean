-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCenteredAdjacencyEuclidean_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:51:12.174752+00:00
-- url     : https://prove2.me/submissions/d86baace-d044-4258-9d4e-e8b2fd44f7a6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightCayleyGraph_lpsQuaternionLabel_isSymmetric


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) :
    (SmallSetExpansion.centeredAdjacencyEuclidean
      (rightCayleyGraph (lpsQuaternionLabel a))
      (Fintype.card (LPSGeneratorIndex p))).IsSymmetric :=
  SmallSetExpansion.centeredAdjacencyEuclidean_isSymmetric
    (rightCayleyGraph (lpsQuaternionLabel a))
    (Fintype.card (LPSGeneratorIndex p))
    (rightCayleyGraph_lpsQuaternionLabel_isSymmetric a)
end QEC.Coding.TannerLiftedProduct
