-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.sourceCycleSection_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:38:07.676851+00:00
-- url     : https://prove2.me/submissions/474b406d-af8d-417c-9299-1b747d4f9ac4

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
    (h : (sourceChainComplex D).middleHomology) :
    (sourceChainComplex D).middleBoundaryInCycles.mkQ
        (sourceCycleSection D h) = h := by
  have hRight := Classical.choose_spec
    ((sourceChainComplex D).middleBoundaryInCycles.mkQ
      |>.exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (Submodule.mkQ_surjective
            (sourceChainComplex D).middleBoundaryInCycles)))
  exact LinearMap.congr_fun hRight h
end QEC.Coding.DistanceBalancing
