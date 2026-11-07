-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFullMeromorphicEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:06:52.075568+00:00
-- url     : https://prove2.me/submissions/ede00043-4cb5-4a9a-8f08-a5aa017542d9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Mathlib.FieldTheory.PrimitiveElement
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    ∀ x : lpsOriginalGeneratedFunctionField N hpos,
      (lpsOriginalGeneratedFullMeromorphicEquiv N hpos hN x).val =
        lpsOriginalHolomorphicFractionToMeromorphicGerm x.val := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  intro x
  rfl
end QEC.Coding.TannerLiftedProduct
