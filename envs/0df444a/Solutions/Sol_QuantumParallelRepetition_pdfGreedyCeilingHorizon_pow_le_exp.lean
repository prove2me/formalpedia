-- Prove2me | solution 1 for QuantumParallelRepetition.pdfGreedyCeilingHorizon_pow_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/7aeb1638-6476-4423-a8a6-b8baa8b2634a

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (n : ℕ) (τ d : ℝ)
    (threshold : 0 < τ)
    (at_most_one : τ ≤ 1) :
    (1 - τ) ^ ⌈d * (n : ℝ) / τ⌉₊ ≤
      Real.exp (-d * (n : ℝ)) := by
  let T : ℕ := ⌈d * (n : ℝ) / τ⌉₊
  have base_nonnegative : 0 ≤ 1 - τ := sub_nonneg.mpr at_most_one
  have base_le : 1 - τ ≤ Real.exp (-τ) := by
    have actual := Real.add_one_le_exp (-τ)
    linarith
  have ceiling : d * (n : ℝ) / τ ≤ (T : ℝ) := by
    exact Nat.le_ceil (d * (n : ℝ) / τ)
  have exponent : -τ * (T : ℝ) ≤ -d * (n : ℝ) := by
    have cleared := (div_le_iff₀ threshold).mp ceiling
    nlinarith
  change (1 - τ) ^ T ≤ Real.exp (-d * (n : ℝ))
  calc
    (1 - τ) ^ T ≤ Real.exp (-τ) ^ T := by
      exact pow_le_pow_left₀ base_nonnegative base_le T
    _ = Real.exp (-τ * (T : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-d * (n : ℝ)) := Real.exp_le_exp.mpr exponent
end QuantumParallelRepetition
