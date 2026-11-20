-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFrobeniusFirstTensorGraphMap_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:53:34.152222+00:00
-- url     : https://prove2.me/submissions/9d01634b-dbde-42c9-b411-f57e528b5d3f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) (K : Type*) [Field K] [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] (a b : K) :
    lpsOriginalFrobeniusFirstTensorGraphMap p K (a ⊗ₜ[ZMod p] b) = a * b^p := by
  rfl
end QEC.Coding.TannerLiftedProduct
