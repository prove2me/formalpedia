-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.HammingWeight_sourceCochainContraction_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:20:35.955642+00:00
-- url     : https://prove2.me/submissions/133ee8f8-8d67-498f-9821-efcc029d0f10

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_HammingWeight_finset_sum_le
import Theorems.Thm_QEC_Coding_HammingWeight_smul_le


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
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (c : Word (ZMod 2) classicalBit) :
    HammingWeight (sourceCochainContraction x c) ≤
      ∑ a : classicalBit, HammingWeight (xOneBitSlice x a) := by
  apply (HammingWeight_finset_sum_le Finset.univ
    (fun a => c a • xOneBitSlice x a)).trans
  apply Finset.sum_le_sum
  intro a _ha
  exact HammingWeight_smul_le (c a) (xOneBitSlice x a)
end QEC.Coding.DistanceBalancing
