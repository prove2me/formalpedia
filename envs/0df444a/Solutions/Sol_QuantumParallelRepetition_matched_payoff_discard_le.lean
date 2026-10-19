-- Prove2me | solution 1 for QuantumParallelRepetition.matched_payoff_discard_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/3be24bd8-2c00-4474-800e-6480abc8444f

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (weight payoff : ι → ℝ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (payoff_le_one : ∀ i, payoff i ≤ 1)
    (matched : ι → Bool) :
    (∑ i, weight i * payoff i) -
        (∑ i, weight i * if matched i then 0 else 1) ≤
      ∑ i, weight i * if matched i then payoff i else 0 := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : matched i = true
  · simp [hi]
  · have hone := payoff_le_one i
    simp only [Bool.not_eq_true] at hi
    simp [hi]
    nlinarith [mul_nonneg (nonnegative i)
      (sub_nonneg.mpr hone)]
end QuantumParallelRepetition
