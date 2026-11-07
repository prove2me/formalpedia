-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.projectedSourceCochain_mem_firstCoboundary_of_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:35:15.159403+00:00
-- url     : https://prove2.me/submissions/6135b54e-a5cf-4f44-8cb3-31bb6a8ae682

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_sourceCochainContraction_le
import Theorems.Thm_QEC_Coding_DistanceBalancing_sum_HammingWeight_xOneBitSlice_le_product
import Theorems.Thm_QEC_Coding_DistanceBalancing_projectedSourceCochain_mem_middleCocycleCode

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
    (hDistance : MiddleCohomologyDistanceAtLeast
      (sourceChainComplex D) d)
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (hWeight : HammingWeight x < d)
    (a : classicalBit) :
    projectedSourceCochain D S x a ∈
      (sourceChainComplex D).firstCoboundaryCheckCode.carrier := by
  by_contra hNonboundary
  have hLower := hDistance (projectedSourceCochain D S x a)
    (projectedSourceCochain_mem_middleCocycleCode D S hS x hx a)
    hNonboundary
  have hUpper : HammingWeight (projectedSourceCochain D S x a) ≤
      HammingWeight x := by
    change HammingWeight
      (sourceCochainContraction x (classicalKernelProjectionWord D S a)) ≤
        HammingWeight x
    exact (HammingWeight_sourceCochainContraction_le
      x (classicalKernelProjectionWord D S a)).trans
        (sum_HammingWeight_xOneBitSlice_le_product x)
  omega
end QEC.Coding.DistanceBalancing
