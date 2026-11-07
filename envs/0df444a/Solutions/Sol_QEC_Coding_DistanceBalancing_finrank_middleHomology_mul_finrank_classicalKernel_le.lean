-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.finrank_middleHomology_mul_finrank_classicalKernel_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:51:15.41393+00:00
-- url     : https://prove2.me/submissions/7ce8cc6c-e5e3-4df2-a1e5-2385fbf38400

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Theorems.Thm_QEC_Coding_DistanceBalancing_tensorHomologyMap_injective

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
    Module.finrank (ZMod 2) (sourceChainComplex D).middleHomology *
        Module.finrank (ZMod 2) (ClassicalKernel D) ≤
      Module.finrank (ZMod 2) (chainComplex D).middleHomology := by
  rw [← Module.finrank_tensorProduct]
  exact LinearMap.finrank_le_finrank_of_injective
    (tensorHomologyMap_injective D)
end QEC.Coding.DistanceBalancing
