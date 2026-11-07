-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.sourceHomologySlice_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:19:28.411308+00:00
-- url     : https://prove2.me/submissions/f9f3aa56-5c4d-452b-8383-c306816ef96f

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (a : classicalBit) :
    sourceHomologySlice D z hz a ≠ 0 ↔
      xOneBitSlice z a ∉
        (sourceChainComplex D).middleBoundaryCode.carrier := by
  constructor
  · intro hClass hBoundary
    apply hClass
    apply (Submodule.Quotient.mk_eq_zero
      (sourceChainComplex D).middleBoundaryInCycles).2
    exact hBoundary
  · intro hBoundary hClass
    apply hBoundary
    exact (Submodule.Quotient.mk_eq_zero
      (sourceChainComplex D).middleBoundaryInCycles).1 hClass
end QEC.Coding.DistanceBalancing
