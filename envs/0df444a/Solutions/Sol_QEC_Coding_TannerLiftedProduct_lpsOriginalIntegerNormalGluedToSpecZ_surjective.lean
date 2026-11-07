-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToSpecZ_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:12:31.043149+00:00
-- url     : https://prove2.me/submissions/663488e6-b789-439a-ad6c-1e6f77a6c28a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_surjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJLineToSpecZ_surjective

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalIntegerNormalGluedToSpecZ N hN) := by
  let := lpsOriginalIntegerNormalGluedToProjectiveJ_surjective N hN
  let := lpsOriginalIntegerProjectiveJLineToSpecZ_surjective
  change Surjective (lpsOriginalIntegerNormalGluedToProjectiveJ N hN ≫
    lpsOriginalIntegerProjectiveJLineToSpecZ)
  infer_instance
end QEC.Coding.TannerLiftedProduct
