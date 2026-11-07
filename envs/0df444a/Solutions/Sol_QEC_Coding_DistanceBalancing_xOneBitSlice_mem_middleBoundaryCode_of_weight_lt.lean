-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.xOneBitSlice_mem_middleBoundaryCode_of_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:38:23.723892+00:00
-- url     : https://prove2.me/submissions/39869841-6ee5-424d-9cec-3c8d3d8d29af

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_xOneBitSlice_le

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
    {d : Nat}
    (hDistance : MiddleHomologyDistanceAtLeast (sourceChainComplex D) d)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hWeight : HammingWeight z < d)
    (a : classicalBit) :
    xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier := by
  by_contra hNonboundary
  have hSliceCycle := xOneBitSlice_mem_middleCycleCode D z hz a
  have hLower := hDistance (xOneBitSlice z a) hSliceCycle hNonboundary
  have hUpper := HammingWeight_xOneBitSlice_le z a
  omega
end QEC.Coding.DistanceBalancing
