-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFrobeniusSecondTensorGraphMap_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:53:24.639548+00:00
-- url     : https://prove2.me/submissions/2d50c319-7806-43ff-b718-3f1c2434492a

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
    lpsOriginalFrobeniusSecondTensorGraphMap p K (a ⊗ₜ[ZMod p] b) = a^p * b := by
  rfl
end QEC.Coding.TannerLiftedProduct
