-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.kernelTensorToSlices_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:38:21.454146+00:00
-- url     : https://prove2.me/submissions/765c5bf6-de3d-4c2b-8cf4-d2bde7ce48d0

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped TensorProduct
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution :
    Function.Injective (kernelTensorToSlices D) := by
  apply Function.Injective.comp
    (TensorProduct.piScalarRight (ZMod 2) (ZMod 2)
      (sourceChainComplex D).middleHomology classicalBit).injective
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (ClassicalKernel D).subtype (ClassicalKernel D).injective_subtype
end QEC.Coding.DistanceBalancing
