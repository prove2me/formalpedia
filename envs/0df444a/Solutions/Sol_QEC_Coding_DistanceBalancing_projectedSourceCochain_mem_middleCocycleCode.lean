-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.projectedSourceCochain_mem_middleCocycleCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:27:58.919823+00:00
-- url     : https://prove2.me/submissions/894e7338-d7d8-4f76-8b92-0e4b142ed5ac

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_sourceCochainContraction_mem_middleCocycleCode
import Theorems.Thm_QEC_Coding_DistanceBalancing_classicalKernelProjectionWord_mem_kernel

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
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (a : classicalBit) :
    projectedSourceCochain D S x a ∈
      (sourceChainComplex D).middleCocycleCode.carrier :=
  sourceCochainContraction_mem_middleCocycleCode D x hx
    (classicalKernelProjectionWord D S a)
    (classicalKernelProjectionWord_mem_kernel D S hS a)
end QEC.Coding.DistanceBalancing
