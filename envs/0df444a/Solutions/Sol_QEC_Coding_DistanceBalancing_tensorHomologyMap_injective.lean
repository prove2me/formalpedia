-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.tensorHomologyMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:42:50.349394+00:00
-- url     : https://prove2.me/submissions/8c0bdbfb-6368-4664-b5e2-75a1dc48029d

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Theorems.Thm_QEC_Coding_DistanceBalancing_kernelTensorToSlices_injective
import Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_comp_tensorHomologyMap

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
    Function.Injective (tensorHomologyMap D) := by
  intro x y hxy
  apply kernelTensorToSlices_injective D
  rw [← homologySliceMap_comp_tensorHomologyMap D]
  exact congrArg (homologySliceMap D) hxy
end QEC.Coding.DistanceBalancing
