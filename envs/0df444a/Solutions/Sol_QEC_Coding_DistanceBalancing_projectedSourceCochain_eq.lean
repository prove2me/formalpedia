-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.projectedSourceCochain_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:33:27.66977+00:00
-- url     : https://prove2.me/submissions/518c2975-c103-4f76-ac85-daa16ac2ee3d

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_sourceCochainContraction_add
import Theorems.Thm_QEC_Coding_DistanceBalancing_sourceCochainContraction_single
import Theorems.Thm_QEC_Coding_DistanceBalancing_sourceCochainContraction_rightInverseImage

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
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (a : classicalBit) :
    projectedSourceCochain D S x a =
      xOneBitSlice x a +
        ∑ b : classicalCheck,
          D.classicalBoundary b a • sourceCochainLift S x b := by
  rw [projectedSourceCochain, classicalKernelProjectionWord,
    sourceCochainContraction_add,
    sourceCochainContraction_single,
    sourceCochainContraction_rightInverseImage D]
end QEC.Coding.DistanceBalancing
