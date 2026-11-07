-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.sum_HammingWeight_xOneBitSlice_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:38:40.180045+00:00
-- url     : https://prove2.me/submissions/8f7b82f4-d2bf-41b8-82f0-e49279b98a93

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_eq_sum_indicator
import Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_inlBlock_eq_sum_xOneBitSlice

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
      (QubitIndex xOne xTwo classicalBit classicalCheck)) :
    (∑ a : classicalBit, HammingWeight (xOneBitSlice z a)) ≤
      HammingWeight z := by
  calc
    (∑ a : classicalBit, HammingWeight (xOneBitSlice z a)) =
        HammingWeight
          (fun p : xOne × classicalBit => z (Sum.inl p)) :=
      (HammingWeight_inlBlock_eq_sum_xOneBitSlice z).symm
    _ ≤ HammingWeight z := by
      rw [HammingWeight_eq_sum_indicator (w := z)]
      rw [Fintype.sum_sum_type]
      rw [HammingWeight_eq_sum_indicator]
      omega
end QEC.Coding.DistanceBalancing
