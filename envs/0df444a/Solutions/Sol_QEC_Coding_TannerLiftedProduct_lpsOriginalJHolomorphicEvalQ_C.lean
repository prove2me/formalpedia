-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJHolomorphicEvalQ_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:31:56.921094+00:00
-- url     : https://prove2.me/submissions/d256fd6c-2fdd-4c8b-b870-b4a898197880

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalQ_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℚ) :
    lpsOriginalJHolomorphicEvalQ (Polynomial.C a) =
      algebraMap ℚ LPSOriginalHolomorphicRing a := by
  apply Subtype.ext
  funext τ
  rw [lpsOriginalJHolomorphicEvalQ_apply, Polynomial.eval₂_C]
  rfl
end QEC.Coding.TannerLiftedProduct
