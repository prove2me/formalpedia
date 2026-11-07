-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.mul_HammingWeight_classicalWordOfHomologyFunctional_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:40:13.142207+00:00
-- url     : https://prove2.me/submissions/c44e0658-ba7d-40b5-a327-6c6e3ddafddd

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_sourceHomologySlice_ne_zero_iff
import Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_eq_sum_indicator
import Theorems.Thm_QEC_Coding_DistanceBalancing_sum_HammingWeight_xOneBitSlice_le

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
    (φ : Module.Dual (ZMod 2) (sourceChainComplex D).middleHomology) :
    d * HammingWeight (classicalWordOfHomologyFunctional D z hz φ) ≤
      HammingWeight z := by
  rw [HammingWeight_eq_sum_indicator, Finset.mul_sum]
  apply (Finset.sum_le_sum fun a _ha => ?_).trans
    (sum_HammingWeight_xOneBitSlice_le z)
  by_cases ha : classicalWordOfHomologyFunctional D z hz φ a ≠ 0
  · rw [if_pos ha, mul_one]
    apply hDistance (xOneBitSlice z a)
      (xOneBitSlice_mem_middleCycleCode D z hz a)
    rw [← sourceHomologySlice_ne_zero_iff D z hz a]
    intro hClass
    apply ha
    change φ (sourceHomologySlice D z hz a) = 0
    rw [hClass]
    exact map_zero φ
  · rw [if_neg ha, mul_zero]
    exact Nat.zero_le (HammingWeight (xOneBitSlice z a))
end QEC.Coding.DistanceBalancing
