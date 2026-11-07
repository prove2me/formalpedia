-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJHolomorphicEvalQ_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:32:41.56264+00:00
-- url     : https://prove2.me/submissions/a79f0f25-913e-47d7-b634-85356d2bcf81

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
theorem _root_.solution :
    lpsOriginalJHolomorphicEvalQ Polynomial.X = lpsOriginalJHolomorphic := by
  apply Subtype.ext
  funext τ
  rw [lpsOriginalJHolomorphicEvalQ_apply, Polynomial.eval₂_X]
  rfl
end QEC.Coding.TannerLiftedProduct
