-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPrefactor_sixtyFour_fourthRoot_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/c7106be2-3e2c-4e3e-a921-5049639bdf85

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution :
    (64 : ℝ) ^ (1 / 4 : ℝ) ≤ 4 := by
  have monotone := Real.rpow_le_rpow
    (by norm_num : (0 : ℝ) ≤ 64)
    (by norm_num : (64 : ℝ) ≤ 256)
    (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ))
  have fourth :
      (256 : ℝ) ^ (1 / 4 : ℝ) = 4 := by
    norm_num
  exact monotone.trans_eq fourth
end QuantumParallelRepetition
