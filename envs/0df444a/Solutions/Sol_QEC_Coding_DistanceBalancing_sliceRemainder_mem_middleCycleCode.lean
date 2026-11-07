-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.sliceRemainder_mem_middleCycleCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:36:57.610848+00:00
-- url     : https://prove2.me/submissions/9c1338a4-66fa-4ace-8fba-7c415cd80d78

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
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    sliceRemainder D z hFill ∈ (chainComplex D).middleCycleCode.carrier := by
  apply (chainComplex D).middleCycleCode.carrier.add_mem hz
  apply (chainComplex D).middleBoundaryCode_le_middleCycleCode
  exact ((chainComplex D).mem_middleBoundaryCode_iff _).2
    ⟨productSliceFilling D z hFill, rfl⟩
end QEC.Coding.DistanceBalancing
