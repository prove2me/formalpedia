-- Prove2me | solution 1 for QuantumParallelRepetition.greedy_terminal_of_log_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/f8fd8976-2c9d-4e33-a7f0-f4a5a0fd09f2

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    {θ η : ℝ} {T : ℕ}
    (hθ : 0 < θ)
    (hη_one : η ≤ 1)
    (hcost : Real.log (1 / θ) < η * (T : ℝ)) :
    (1 - η) ^ T < θ := by
  have hbase : 1 - η ≤ Real.exp (-η) := by
    have h := Real.add_one_le_exp (-η)
    linarith
  have hpow :
      (1 - η) ^ T ≤ Real.exp (-η) ^ T :=
    pow_le_pow_left₀ (sub_nonneg.mpr hη_one) hbase T
  have hlog : -η * (T : ℝ) < Real.log θ := by
    rw [one_div, Real.log_inv] at hcost
    linarith
  calc
    (1 - η) ^ T ≤ Real.exp (-η) ^ T := hpow
    _ = Real.exp (-η * (T : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ < θ := (Real.exp_lt_exp.mpr hlog).trans_eq
      (Real.exp_log hθ)
end QuantumParallelRepetition
