-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJHolomorphicEvalQ_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:58:40.907508+00:00
-- url     : https://prove2.me/submissions/a49d02e5-65be-4c6b-8357-0a5e201475e8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (P : Polynomial ℚ) (τ : ℍ) :
    (lpsOriginalJHolomorphicEvalQ P).val τ=P.eval₂ (algebraMap ℚ ℂ) (lpsOriginalJInvariant τ) := by
  change (lpsOriginalJHolomorphicEval (P.map (algebraMap ℚ ℂ))).val τ=_
  rw [lpsOriginalJHolomorphicEval_apply,Polynomial.eval_map]
end QEC.Coding.TannerLiftedProduct
