-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.HammingWeight_inlBlock_eq_sum_xOneBitSlice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:36:46.477208+00:00
-- url     : https://prove2.me/submissions/0913e923-f87c-4e84-aa3f-43662b7052f2

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_eq_sum_indicator

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
    HammingWeight (fun p : xOne × classicalBit => z (Sum.inl p)) =
      ∑ a : classicalBit, HammingWeight (xOneBitSlice z a) := by
  rw [HammingWeight_eq_sum_indicator]
  simp_rw [HammingWeight_eq_sum_indicator]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm
end QEC.Coding.DistanceBalancing
