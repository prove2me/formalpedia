-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.homologySliceMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:21:42.202196+00:00
-- url     : https://prove2.me/submissions/bedc437b-dbc4-4d49-bf12-ac9bf12a3576

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
theorem _root_.solution
    (z : (chainComplex D).middleCycleCode.carrier) :
    homologySliceMap D
        ((chainComplex D).middleBoundaryInCycles.mkQ z) =
      cycleToHomologySlices D z := by
  rfl
end QEC.Coding.DistanceBalancing
