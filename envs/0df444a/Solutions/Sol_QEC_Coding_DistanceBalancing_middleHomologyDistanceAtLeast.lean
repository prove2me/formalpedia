-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.middleHomologyDistanceAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:53:57.470505+00:00
-- url     : https://prove2.me/submissions/707a849c-eb02-463d-93f2-7e282344d82e

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_xOneBitSlice_mem_middleBoundaryCode_of_weight_lt
import Theorems.Thm_QEC_Coding_DistanceBalancing_mem_middleBoundaryCode_of_slices

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
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    {d : Nat}
    (hDistance : MiddleHomologyDistanceAtLeast (sourceChainComplex D) d) :
    MiddleHomologyDistanceAtLeast (chainComplex D) d := by
  intro z hz hNonboundary
  by_contra hNotLower
  have hWeight : HammingWeight z < d := by omega
  have hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈
        (sourceChainComplex D).middleBoundaryCode.carrier := by
    intro a
    exact xOneBitSlice_mem_middleBoundaryCode_of_weight_lt
      D hDistance z hz hWeight a
  exact hNonboundary (mem_middleBoundaryCode_of_slices D S hS z hz hFill)
end QEC.Coding.DistanceBalancing
