-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedTriangularTerm_neg_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:34:35.208911+00:00
-- url     : https://prove2.me/submissions/af10b66c-92b6-47c3-9721-1ca481e77332

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiHalfTriangularDegree_neg_sub_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedTriangularWeight_neg_sub_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution (z : ℤ) :
    signedTriangularTerm (-z - 1) = signedTriangularTerm z := by
  rw [signedTriangularTerm, signedTriangularTerm,
    jacobiHalfTriangularDegree_neg_sub_one,
    signedTriangularWeight_neg_sub_one]
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
