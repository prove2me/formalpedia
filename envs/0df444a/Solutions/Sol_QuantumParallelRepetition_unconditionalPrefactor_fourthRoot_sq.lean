-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPrefactor_fourthRoot_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/2162ef01-26c0-439a-bab2-90ce0fc96053

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {a : ℝ} (nonnegative : 0 ≤ a) :
    (a ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt a := by
  calc
    (a ^ (1 / 4 : ℝ)) ^ 2 = a ^ ((1 / 4 : ℝ) * 2) :=
      (Real.rpow_mul_natCast nonnegative (1 / 4 : ℝ) 2).symm
    _ = a ^ (1 / 2 : ℝ) := by norm_num
    _ = Real.sqrt a := (Real.sqrt_eq_rpow a).symm
end QuantumParallelRepetition
